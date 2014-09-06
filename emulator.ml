open Bigarray
open Risc

type error = 
  | BusError of int 
  | InvalidReg
  | Illegal of int
  | ChkError 
  | BrkError 
  | Exit of Int32.t

exception Error of error

let new_cell sz al = { Gcmap.size = sz; Gcmap.live = al }

exception Found of Int32.t

let array_create n =
  let res = Array1.create int32 c_layout n in
    for i = 0 to n - 1 do
      res.{i} <- Int32.zero
    done;
    res

let array_get t i =
  t.{i}

let array_set t i v =
  t.{i} <- v

class gc = 
  let mask_align = Int32.shift_left (Int32.of_int 0x3fffffff) 2 in
  let three = Int32.of_int 3 in
  let four = Int32.of_int 4 in
  let align n = Int32.logand n mask_align in
  let round n = align (Int32.add n three) in
    fun verbose ->
object(self)
  val mutable alive_cells = Gcmap.empty
  val mutable dead_cells = Gcmap.empty
  val stack = Stack.create ()
  val mutable hp_address = Int32.zero
  val mutable hp_size = Int32.zero
  val mutable sp = 0
  method init hp sz reg emu =
    if (Int32.compare hp Int32.zero < 0) || (Int32.compare hp (Int32.of_int emu#getMemSize) >= 0) then
      failwith ("out of bounds heap start: "^(Int32.to_string hp))
    else if (Int32.compare (Int32.add hp sz) (Int32.of_int emu#getMemSize) > 0) then
      failwith ("out of bounds heap end: "^(Int32.to_string (Int32.add hp sz)))
    else if (Int32.compare sz Int32.zero < 0) then
      failwith ("negative heap size: "^(Int32.to_string sz));
    let sz = 
      if Int32.compare sz Int32.zero = 0 then Int32.of_int emu#getMemSize
      else Int32.add sz hp
    in
    let hp = round hp in
    let sz = min sz (Int32.of_int emu#getMemSize) in
    let sz = max Int32.zero (Int32.sub sz hp) in
    let sz = align sz in
      hp_address <- hp;
      hp_size <- sz;
      sp <- reg;
      if verbose then
	begin
	  prerr_string "[GC]";
	  prerr_string "heap address = ";prerr_string (Int32.to_string hp_address);prerr_string ", ";
	  prerr_string "heap size = ";prerr_string (Int32.to_string hp_size);prerr_string " bytes, ";
	  if(sp = 0) then prerr_string "no stack pointer"
	  else (prerr_string "stack pointer = ";prerr_int sp);
	  prerr_newline()
	end;
      alive_cells <- Gcmap.empty;
      dead_cells <- Gcmap.add hp_address (new_cell hp_size false) (Gcmap.empty)
	(*
	  method alloc sz emu =
	  if (sz < 0) then failwith ("negative block size: "^(string_of_int sz));
	  let sz = max 4 (round sz) in
	  let addr = hp_address in
	  hp_address <- hp_address + sz;
	  addr
	*)
  method alloc sz emu =
    if (Int32.compare sz Int32.zero < 0) then failwith ("negative block size: "^(Int32.to_string sz));
    let sz = max four (round sz) in
      match self#lock sz with
	| Some(addr) -> addr
	| None -> 
	    begin
	      self#free emu;
	    match self#lock sz with
	      | Some(addr) -> addr
	      | None -> failwith ("could not allocate block of "^(Int32.to_string sz)^" bytes")
	    end
  method private mark addr =
    try
      let c = Gcmap.find addr alive_cells in
	if not (c.Gcmap.live) then
	  begin
	    c.Gcmap.live <- true;
	    Stack.push (addr,c) stack;
	  end
    with Not_found -> ()
  method private free emu =
    let usage1 = ref Int32.zero in
      Gcmap.iter (fun addr c ->
		      c.Gcmap.live <- false;
		      usage1 := Int32.add (!usage1) c.Gcmap.size) alive_cells;
      let stk_address = 
	if sp = 0 then (Int32.add hp_address hp_size)
	else (emu#readReg sp)
      in
      let mem_size = Int32.of_int emu#getMemSize in
      let stk_address = align stk_address in
	if Int32.compare stk_address (Int32.add hp_address hp_size) < 0 then
	  failwith "stack overwrote heap";
	for i = 0 to 31 do
	  self#mark (emu#readReg i)
	done;
	let i = ref Int32.zero in
	  while Int32.compare !i hp_address < 0 do
	    self#mark (emu#readWord (Int32.to_int !i));
	    i := Int32.add (!i) four
	  done;
	  i := stk_address;
	  while Int32.compare !i mem_size < 0 do
	    self#mark (emu#readWord (Int32.to_int !i));
	    i := Int32.add (!i) four
	  done;
	  while not (Stack.is_empty stack) do
	    let (address,c) = Stack.pop stack in
	      i := address;
	      while Int32.compare !i (Int32.add address c.Gcmap.size) < 0 do
		self#mark (emu#readWord (Int32.to_int !i));
		i := Int32.add (!i) four
	      done
	  done;
	  let usage2 = ref Int32.zero in
	    Gcmap.iter (fun addr c ->
			    if c.Gcmap.live then
			      usage2 := Int32.add (!usage2) c.Gcmap.size
			    else
			      begin
				alive_cells <- Gcmap.remove addr alive_cells;
				self#add_dead addr c
			      end)
	      alive_cells;
	    if verbose then
	      begin
		prerr_string "[GC]";
		prerr_string (Int32.to_string (!usage1));
		prerr_string " bytes -> ";
		prerr_string (Int32.to_string (!usage2));
		prerr_string " bytes";
		prerr_newline()
	      end
  method private add_dead addr c =
    let addr' = Int32.add addr c.Gcmap.size in
      dead_cells <- Gcmap.add_or_join addr addr' c dead_cells
(*
    try

      let c' = Gcmap.find addr' dead_cells in
	c.Gcmap.size <- c.Gcmap.size + c'.Gcmap.size;
	dead_cells <- Gcmap.add addr c (Gcmap.remove addr' dead_cells)
    with Not_found ->
      dead_cells <- Gcmap.add addr c dead_cells
*)
  method private lock sz =
    try
      Gcmap.iter (fun addr c ->
		      if Int32.compare c.Gcmap.size sz >= 0 then
			if Int32.compare c.Gcmap.size sz = 0 then
			  begin
			    c.Gcmap.live <- false;
			    dead_cells <- Gcmap.remove addr dead_cells;
			    alive_cells <- Gcmap.add addr c alive_cells;
			    raise (Found(addr))
			  end
			else
			  begin
			    c.Gcmap.size <- Int32.sub c.Gcmap.size sz;
			    dead_cells <- Gcmap.add (Int32.add addr sz) c (Gcmap.remove addr dead_cells);
			    alive_cells <- Gcmap.add addr (new_cell sz true) alive_cells;
			    raise (Found(addr))
			  end) dead_cells;
      if verbose then prerr_string "[GC]no cell allocated\n";
      None
    with
	Found(addr) -> 
	  if verbose then
	    begin
	      prerr_string "[GC]";
	      prerr_string "cell allocated: ";
	      prerr_string (Int32.to_string addr);
	      prerr_newline()
	    end;
	  Some(addr)
end
and emulator = 
  let create_memory mem_size = 
    array_create mem_size 
(*
    let mem = Array1.create int32 c_layout mem_size in
      for i = 0 to mem_size - 1 do
	mem.{i} <- Int32.zero
      done;
      mem
*)
  in
  let int_op_of_arith_op = function
    | Add -> Int32.add
    | Sub -> Int32.sub
    | Mul -> Int32.mul
    | Div -> Int32.div
    | Cmp -> (fun a b -> Int32.of_int (Int32.compare a b))
    | Mod -> Int32.rem
  and int_op_of_log_op = function
    | And -> Int32.logand
    | Or -> Int32.logor
    | Xor -> Int32.logxor
    | Bic -> (fun a b -> Int32.logand a (Int32.lognot b))
  and int_op_of_sh_op = function
    | Lsh -> (fun a b -> 
		let b = Int32.to_int b in
		  if b > 0 then Int32.shift_left a b 
		  else Int32.shift_right_logical a (-b))
    | Ash -> (fun a b -> 
		let b = Int32.to_int b in
		  if b > 0 then Int32.shift_left a b 
		  else Int32.shift_right a (-b))
  and cond_of_test_op = function
    | Beq -> (fun a -> Int32.compare a Int32.zero = 0)
    | Bne -> (fun a -> Int32.compare a Int32.zero <> 0)
    | Blt -> (fun a -> Int32.compare a Int32.zero < 0)
    | Bge -> (fun a -> Int32.compare a Int32.zero >= 0)
    | Bgt -> (fun a -> Int32.compare a Int32.zero > 0)
    | Ble -> (fun a -> Int32.compare a Int32.zero <= 0)
  in
    fun code mem_size ->
object(self)
  val memory = create_memory mem_size 
  val mutable pc = 0
  val registers = Array.make 32 (Int32.zero)
  val gc = new gc false
  method private init =
    code#iter 
      (fun i instr ->
	 array_set memory i (Codec.code_instruction instr))
  method getMemSize = 4 * mem_size
  method readWord adr =
    if adr land 0x3 <> 0 then raise (Error(BusError(adr)))
    else
      try
	array_get memory (adr lsr 2)
      with Invalid_argument(_) -> raise (Error(BusError(adr)))
  method readByte adr =
    let b = self#readWord ((adr lsr 2) lsl 2) in
    let num = 3 - (adr land 0x3) in
      Int32.logand (Int32.shift_right_logical b (8*num)) (Int32.of_int 0xff)
  method writeWord adr w =
    if adr land 0x3 <> 0 then raise (Error(BusError(adr)))
    else
      try
	array_set memory (adr lsr 2) w
      with Invalid_argument(_) -> raise (Error(BusError(adr)))
  method writeByte adr b =
    let w = self#readWord ((adr lsr 2) lsl 2) in
    let num = 3 - (adr land 0x3) in
    let mask = Int32.lognot (Int32.shift_left (Int32.of_int 0xff) (8*num)) in
    let w = Int32.logand w mask in
    let w = Int32.logor w (Int32.shift_left (Int32.logand b (Int32.of_int 0xff)) (8*num)) in
      self#writeWord ((adr lsr 2) lsl 2) w
  method getPC = pc
  method setPC pc' = pc <- pc'
  method readReg n = 
    if (0 <= n) && (n < 32) then registers.(n)
    else raise (Error(InvalidReg))
  method writeReg n w =
    if (0 < n) && (n < 32) then registers.(n) <- w
    else if n = 0 then ()
    else raise (Error(InvalidReg))
  method fetch pc =
    Codec.decode_instruction (self#readWord pc)
  method exec instr pc =
    let val_of_ic (Signed(f)) = Int32.of_int (f ())
    and val_of_oc (Relative(f)) = f () 
    and val_of_lc (Absolute(f)) = f ()
    and val_of_ariiu = function
      | AR(R(n)) -> self#readReg n
      | AI(Signed(f)) -> Int32.of_int (f ())
      | AIU(Unsigned(f)) -> Int32.of_int (f ())
    and val_of_bri = function
      | BR(R(n)) -> self#readReg n
      | BI(Signed(f)) -> Int32.of_int (f ())
    in
      match instr with
	| IArith(op,R(a),R(b),c) -> 
	    self#writeReg a ((int_op_of_arith_op op) (self#readReg b) (val_of_ariiu c));
	    pc + 4
	| ILog(op,R(a),R(b),c) -> 
	    self#writeReg a ((int_op_of_log_op op) (self#readReg b) (val_of_ariiu c));
	    pc + 4
	| ISh(op,R(a),R(b),c) -> 
	    self#writeReg a ((int_op_of_sh_op op) (self#readReg b) (val_of_bri c));
	    pc + 4
	| IMem(Ldw,R(a),R(b),ic) ->
	      self#writeReg a (self#readWord (Int32.to_int (Int32.add (self#readReg b) (val_of_ic ic))));
	    pc + 4
	| IMem(Ldb,R(a),R(b),ic) ->
	      self#writeReg a (self#readByte (Int32.to_int (Int32.add (self#readReg b) (val_of_ic ic))));
	    pc + 4
	| IMem(Stw,R(a),R(b),ic) ->
	    self#writeWord (Int32.to_int (Int32.add (self#readReg b) (val_of_ic ic))) (self#readReg a);
	    pc + 4
	| IMem(Stb,R(a),R(b),ic) ->
	    self#writeByte (Int32.to_int (Int32.add (self#readReg b) (val_of_ic ic))) (Int32.logand (self#readReg a) (Int32.of_int 0xff));
	    pc + 4
	| IMem(Psh,R(a),R(b),ic) ->
	    self#writeReg b (Int32.sub (self#readReg b) (val_of_ic ic));
	    self#writeWord (Int32.to_int (self#readReg b)) (self#readReg a);
	    pc + 4
	| IMem(Pop,R(a),R(b),ic) ->
	    self#writeReg a (self#readWord (Int32.to_int (self#readReg b)));
	    self#writeReg b (Int32.add (self#readReg b) (val_of_ic ic));
	    pc + 4
	| ITest(op,R(a),oc) ->
	    pc + 4 * (if cond_of_test_op op (self#readReg a) then val_of_oc oc else 1)
	| Chk(R(a),c) ->
	    let a = (self#readReg a) and c = val_of_ariiu c in
	    if (Int32.compare a Int32.zero >= 0) && (Int32.compare a c) < 0 
	    then pc + 4
	    else raise (Error(ChkError))
	| Bsr(oc) ->
	    self#writeReg 31 (Int32.of_int (pc + 4));
	    pc + 4 * (val_of_oc oc)
	| Jsr(lc) -> 
	    self#writeReg 31 (Int32.of_int (pc + 4));
	    4 * (val_of_lc lc)
	| Ret(R(a)) -> 
	    let a = Int32.to_int (self#readReg a) in
	      if a = 0 then raise (Error(Exit(Int32.of_int a)))
	      else a
	| Break -> raise (Error(BrkError))
	| Syscall(R(a),R(b),syscall) -> 
	    begin
	      match syscall with
		| Sys_io_rd_chr -> 
		    let n = 
		      try
		       Char.code (Pervasives.input_char stdin)
		      with
			 End_of_file -> -1
		    in
		      self#writeReg a (Int32.of_int n)
		| Sys_io_rd_int -> 
		    let s = Pervasives.input_line stdin in
		      self#writeReg a (Int32.of_string s)
		| Sys_io_wr_chr -> 
		    let n = (Int32.to_int (self#readReg a)) land 0xff in
		      Pervasives.output_char stdout (Char.chr n)
		| Sys_io_wr_int -> 
		    Pervasives.output_string stdout (Int32.to_string (self#readReg a))
		| Sys_gc_init -> 
		    let a = (self#readReg a) in
		    let b = self#readReg b in
		    let sz = (Int32.logand b (Int32.of_int 0x1ffffff))
		    and sp = Int32.to_int (Int32.shift_right_logical b 27)
		    in
		      gc#init a (Int32.mul sz 4l) sp (self:>emulator)
		| Sys_gc_alloc -> 
		    let sz = (self#readReg b) in
		      self#writeReg a (gc#alloc sz (self:>emulator))
		| Sys_get_total_mem_size -> 
		    self#writeReg a (Int32.of_int (self#getMemSize))
		| Sys_io_flush -> 
		    Pervasives.flush stdout
		| Sys_exit -> 
		    raise (Error(Exit(self#readReg a)))
	    end;
	    pc + 4
	| Data(_) -> raise (Error(Illegal(pc)))
  method start =
    while true do
(*       prerr_int pc;prerr_newline(); *)
      let instr = self#fetch pc in
	pc <- self#exec instr pc
    done
  initializer
    self#init
end
