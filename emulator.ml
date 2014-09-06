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

type cell = { mutable address : int; mutable size : int; mutable alive: bool }

let new_cell addr sz al = { address = addr; size = sz; alive = al }

let string_of_bool = function
  | true -> "true"
  | false -> "false"

let string_of_cell c =
  "address: "^(string_of_int c.address)^
  ", size: "^(string_of_int c.size)^
  ", alive: "^(string_of_bool c.alive)

module CellSet = Set.Make(struct
			    type t = cell
			    let compare cx cy =
			      Pervasives.compare cx.address cy.address
			  end)

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
  let align n = n land 0x7ffffffc in
  let round n = align (n + 3) in
    fun verbose ->
object(self)
  val mutable alive_cells = CellSet.empty
  val mutable dead_cells = CellSet.empty
  val stack = Stack.create ()
  val mutable hp_address = 0
  val mutable hp_size = 0
  val mutable sp = 0
  method init hp sz reg emu =
    if (hp < 0) || (hp >= emu#getMemSize) then
      failwith ("out of bounds heap start: "^(string_of_int hp))
    else if (hp + sz - 1 >= emu#getMemSize) then
      failwith ("out of bounds heap end: "^(string_of_int (hp + sz - 1)))
    else if (sz < 0) then
      failwith ("negative heap size: "^(string_of_int sz));
    let sz = 
      if sz = 0 then emu#getMemSize
      else sz + hp
    in
    let hp = round hp in
    let sz = min sz emu#getMemSize in
    let sz = max 0 (sz - hp) in
    let sz = align sz in
      hp_address <- hp;
      hp_size <- sz;
      sp <- reg;
      if verbose then
	begin
	  prerr_string "[GC]";
	  prerr_string "heap address = ";prerr_int hp_address;prerr_string ", ";
	  prerr_string "heap size = ";prerr_int hp_size;prerr_string " bytes, ";
	  if(sp = 0) then prerr_string "no stack pointer"
	  else (prerr_string "stack pointer = ";prerr_int sp);
	  prerr_newline()
	end;
      alive_cells <- CellSet.empty;
      dead_cells <- CellSet.singleton (new_cell hp_address hp_size false)
(*
  method alloc sz emu =
    if (sz < 0) then failwith ("negative block size: "^(string_of_int sz));
    let sz = max 4 (round sz) in
    let addr = hp_address in
      hp_address <- hp_address + sz;
      addr
*)
  method alloc sz emu =
    if (sz < 0) then failwith ("negative block size: "^(string_of_int sz));
    let sz = max 4 (round sz) in
      match self#lock sz with
	| Some(c) -> self#zero c emu; c.address
	| None -> 
	    begin
	      self#free emu;
	    match self#lock sz with
	      | Some(c) -> self#zero c emu; c.address
	      | None -> failwith ("could not allocate block of "^(string_of_int sz)^" bytes")
	    end
  method private zero c emu =
    for i = 0 to (c.size / 4) - 1 do
      emu#writeWord (c.address+4*i) (Int32.zero)
    done
  method private mark addr =
    try
      let c = CellSet.find (new_cell addr 0 false) alive_cells in
	if not (c.alive) then
	  begin
	    c.alive <- true;
	    Stack.push c stack;
	  end
    with Not_found -> ()
  method private free emu =
    let usage1 = ref 0 in
      CellSet.iter (fun c ->
		      c.alive <- false;
		      usage1 := (!usage1) + c.size) alive_cells;
      let stk_address = 
	if sp = 0 then hp_address + hp_size 
	else (Int32.to_int (emu#readReg sp))
      in
      let mem_size = emu#getMemSize in
      let stk_address = align stk_address in
	if stk_address < hp_address + hp_size then
	  failwith "stack overwrote heap";
	for i = 0 to 31 do
	  self#mark (Int32.to_int (emu#readReg i))
	done;
	let i = ref 0 in
	  while !i < hp_address do
	    self#mark (Int32.to_int (emu#readWord (!i)));
	    i := (!i) + 4
	  done;
	  i := stk_address;
	  while !i < mem_size do
	    self#mark (Int32.to_int (emu#readWord (!i)));
	    i := (!i) + 4
	  done;
	  while not (Stack.is_empty stack) do
	    let c = Stack.pop stack in
	      i := c.address;
	      while !i < c.address + c.size do
		self#mark (Int32.to_int (emu#readWord (!i)));
		i := (!i) + 4
	      done
	  done;
	  let usage2 = ref 0 in
	    CellSet.iter (fun c ->
			    if c.alive then
			      usage2 := (!usage2) + c.size
			    else
			      begin
				alive_cells <- CellSet.remove c alive_cells;
				dead_cells <- CellSet.add c dead_cells
			      end)
	      alive_cells;
	    if verbose then
	      begin
		prerr_string "[GC]";
		prerr_int (!usage1);
		prerr_string " bytes -> ";
		prerr_int (!usage2);
		prerr_string " bytes";
		prerr_newline()
	      end
  method private lock sz =
    let cell,last = CellSet.fold 
		 (fun c (cell,last) ->
		    match cell with
		      | Some(_) -> cell,last
		      | None ->
			  let c = 
			    match last with
			      | Some(c') ->
				  if c'.address + c'.size = c.address then
				    begin
				      dead_cells <- CellSet.remove c dead_cells;
				      c'.size <- c'.size + c.size;
				      c'
				    end
				  else c
			      | None -> c
			  in
			    if c.size >= sz then
			      let cell = 
				if c.size = sz then
				  begin
				    c.alive <- false;
				    dead_cells <- CellSet.remove c dead_cells;
				    c
				  end
				else
				  begin
				    c.address <- c.address + sz;
				    c.size <- c.size - sz;
				    new_cell (c.address - sz) sz true
				  end
			      in
				alive_cells <- CellSet.add cell alive_cells;
				Some(cell),last
			    else
			      cell,Some(c))
		      dead_cells (None,None) 
    in
      if verbose then
	begin
	  prerr_string "[GC]";
	  (match cell with 
	     | None -> 
		 prerr_string "no cell allocated";
	     | Some(c) ->
		 prerr_string "cell allocated: ";
		 prerr_string (string_of_cell c)
	  );
	  prerr_newline()
	end;
      cell
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
		    let a = Int32.to_int (self#readReg a) in
		    let b = self#readReg b in
		    let sz = Int32.to_int (Int32.logand b (Int32.of_int 0x1ffffff))
		    and sp = Int32.to_int (Int32.shift_right_logical b 27)
		    in
		      gc#init a (4*sz) sp (self:>emulator)
		| Sys_gc_alloc -> 
		    let sz = Int32.to_int (self#readReg b) in
		      self#writeReg a (Int32.of_int (gc#alloc sz (self:>emulator)))
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
      (* prerr_int pc;prerr_newline(); *)
      let instr = self#fetch pc in
	pc <- self#exec instr pc
    done
  initializer
    self#init
end
