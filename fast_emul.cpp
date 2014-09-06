(*

#define MASK_SZ 0x1ffffffl
#define MASK_REG 0x1fl
#define MASK_IMM 0xffffl
#define MASK_REL 0x1fffffl
#define MASK_ABS 0x3ffffffl

#define DEBUG(e)

#define INCRPC(i) pc := Int32.add (i) (!pc)

#define INTOP(op) \
  (match mode with | R -> (function n -> \
  let c = Int32.logand n MASK_REG in \
  let n = Int32.shift_right_logical n 16 in \
  let b = Int32.logand n MASK_REG in \
  let n = Int32.shift_right_logical n 5 in \
  let a = Int32.logand n MASK_REG in \
  register_set a (op (register_get b) (register_get c)); \
  INCRPC(4l)) \
  | I -> \
  (function n -> \
  let c = Int32.logand n MASK_IMM in \
  let c = Int32.shift_right (Int32.shift_left c 16) 16 in (* 16 = 32 - 16 *) \
  let n = Int32.shift_right_logical n 16 in \
  let b = Int32.logand n MASK_REG in \
  let n = Int32.shift_right_logical n 5 in \
  let a = Int32.logand n MASK_REG in \
  register_set a (op (register_get b) c); \
  INCRPC(4l)) \
  | IU -> \
  (function n -> \
  let c = Int32.logand n MASK_IMM in \
  let n = Int32.shift_right_logical n 16 in \
  let b = Int32.logand n MASK_REG in \
  let n = Int32.shift_right_logical n 5 in \
  let a = Int32.logand n MASK_REG in \
  register_set a (op (register_get b) c); \
  INCRPC(4l)) \
  | Rel | Abs | Other -> assert false)

#define MEMOP(op) \
  (fun n -> \
  let c = Int32.logand MASK_IMM n in \
  let c = Int32.shift_right (Int32.shift_left c 16) 16 in (* 16 = 32 - 16 *) \
  let n = Int32.shift_right_logical n 16 in \
  let b = Int32.logand MASK_REG n in \
  let n = Int32.shift_right_logical n 5 in \
  let a = Int32.logand MASK_REG n in \
  op; \
  INCRPC(4l))

#define TESTOP(op) \
  (fun n -> \
  let c = Int32.logand n MASK_REL in \
  let c = Int32.shift_right (Int32.shift_left c 11) 11 in (* 11 = 32 - 21 *) \
  let n = Int32.shift_right_logical n 21 in \
  let a = Int32.logand n MASK_REG in \
  INCRPC(Int32.mul op 4l))

*)

open Bigarray

module type Code =
  sig
    val mem_size : int
    val code : Risc.code_generator
  end

module type Emulator =
  sig
    type error = Illegal | BrkExn | ChkExn | Exit of Int32.t | Syscall of Int32.t * Int32.t * int

    exception Error of error

    val mem_size : int
    val register_get : Int32.t -> Int32.t
    val register_set : Int32.t -> Int32.t -> unit
    val read_word : Int32.t -> Int32.t
    val write_word : Int32.t -> Int32.t -> unit
    val getPC : unit -> Int32.t
    val setPC : Int32.t -> unit
    val reset : unit -> unit
    val tick : unit -> unit
    val exec : unit -> unit
  end

module Make(Code:Code) : Emulator =
  struct
    type error = Illegal | BrkExn | ChkExn | Exit of Int32.t | Syscall of Int32.t * Int32.t * int

    let int32_compare a b = Int32.to_int (Int32.sub (Int32.sub a b) (Int32.sub b a))

    exception Error of error

    let pc = ref 0l

    let getPC () = !pc
    let setPC v = pc := v

    let registers = Array.create 32 0l

    let register_get i =
      DEBUG(prerr_string "getting register ";prerr_string (Int32.to_string i);prerr_newline();)
      registers.(Int32.to_int i)

    let register_set i v =
      DEBUG(prerr_string "setting register ";prerr_string (Int32.to_string i);prerr_string " to value ";prerr_string (Int32.to_string v);prerr_newline();)
    let i = Int32.to_int i in
      if i > 0 then registers.(i) <- v

    let mem_size = Code.mem_size

    let mem_size_int32 = Int32.mul 4l (Int32.of_int mem_size)

    let memory = Array1.create int32 c_layout mem_size

    let memory_get i = memory.{Int32.to_int i}

    let memory_set i v = memory.{Int32.to_int i} <- v

    let read_word addr =
      DEBUG(prerr_string "reading word at ";prerr_string (Int32.to_string addr);prerr_newline();)
	memory_get (Int32.shift_right addr 2)

    let write_word addr v =
      DEBUG(prerr_string "writting word at ";prerr_string (Int32.to_string addr);prerr_string ": ";prerr_string (Int32.to_string v);prerr_newline();)
	memory_set (Int32.shift_right addr 2) v

    let read_byte =
      let shift = [|24;16;8;0|] in
	function addr ->
	  Int32.logand
	  (Int32.of_int 0xff)
	  (Int32.shift_right_logical (read_word addr) (shift.(0x3 land (Int32.to_int addr))))

    let write_byte =
      let shift = [|24;16;8;0|] in
      let mask = [|0l;0l;0l;0l|] in
	for i = 0 to 3 do
	  mask.(i) <- Int32.lognot (Int32.shift_left (Int32.of_int 0xff) (shift.(i)))
	done;
	fun addr v ->
	  let i = 0x3 land (Int32.to_int addr) in
	    write_word addr
	      (Int32.logor
		 (Int32.logand (mask.(i)) (read_word addr))
		 (Int32.shift_left (Int32.logand v (Int32.of_int 0xff)) (shift.(i))))


    type instruction =
      | Add | Sub | Mul | Div | Cmp | Mod
      | And | Or | Xor | Bic
      | Lsh | Ash
      | Ldw | Ldb | Stw | Stb | Pop | Psh
      | Beq | Bne | Blt | Bge | Bgt | Ble
      | Chk
      | Bsr | Jsr | Ret
      | Break | Sys

    type mode = R | I | IU | Rel | Abs | Other

    let get_op_table =
      let instrs =
	let arith = [0,Add; 1,Sub; 2,Mul; 3,Div; 4,Mod; 5,Cmp]
	in
	let arith = (List.map (fun (x,y) -> (x,y,R)) arith) @
		    (List.map (fun (x,y) -> (16+x,y,I)) arith) @
		    (List.map (fun (x,y) -> (54+x,y,IU)) arith)
	in
	let log = [8,Or;9,And;10,Bic;11,Xor] in
	let log = (List.map (fun (x,y) -> (x,y,R)) log) @
		  (List.map (fun (x,y) -> (16+x,y,I)) log) @
		  (List.map (fun (x,y) -> (52+x,y,IU)) log)
	in
	let sh = [12,Lsh;13,Ash] in
	let sh = (List.map (fun (x,y) -> (x,y,R)) sh) @
		 (List.map (fun (x,y) -> (x+16,y,I)) sh)
	in
	let chk = [14,Chk,R;30,Chk,I;39,Chk,IU] in
	let mem = [32,Ldw;33,Ldb;34,Pop;36,Stw;37,Stb;38,Psh] in
	let mem = List.map (fun (x,y) -> (x,y,I)) mem in
	let test = [40,Beq;41,Bne;42,Blt;43,Bge;44,Ble;45,Bgt] in
	let test = List.map (fun (x,y) -> (x,y,Rel)) test in
	let bsr = [46,Bsr,Rel] and jsr = [48,Jsr,Abs] and ret = [49,Ret,Other] in
	let brk = [6,Break,Other] and sysc = [7,Sys,Other] in
	  arith@log@sh@chk@mem@test@bsr@jsr@ret@brk@sysc
      in
      let size = 1 lsl 6 in
      let ops = Array.create size (fun _ -> raise (Error(Illegal))) in
      let iadd a b = Int32.add a b
      and isub a b = Int32.sub a b
      and imul a b = Int32.mul a b
      and idiv a b = Int32.div a b
      and imod a b = Int32.rem a b
      and icmp a b = Int32.sub (Int32.sub a b) (Int32.sub b a)
      and iand a b = Int32.logand a b
      and ior a b = Int32.logor a b
      and ixor a b = Int32.logxor a b
      and ibic a b = Int32.logand a (Int32.lognot b)
      and ilsh a b =
	let b = Int32.to_int b in
	  if b < 0 then Int32.shift_right_logical a ((-b) land 0x1f)
	  else Int32.shift_left a (b land 0x1f)
      and iash a b =
	let b = Int32.to_int b in
	  if b < 0 then Int32.shift_right a ((-b) land 0x1f)
	  else Int32.shift_left a (b land 0x1f)
      in
	for i = 0 to size - 1 do
	  try
	    let (_,op,mode) = List.find (fun (x,_,_) -> x = i) instrs in
	      ops.(i) <-
	      match op with
		| Add -> INTOP(iadd)
		| Sub -> INTOP(isub)
		| Mul -> INTOP(imul)
		| Div -> INTOP(idiv)
		| Cmp -> INTOP(icmp)
		| Mod -> INTOP(imod)
		| And -> INTOP(iand)
		| Or -> INTOP(ior)
		| Xor -> INTOP(ixor)
		| Bic -> INTOP(ibic)
		| Lsh -> INTOP(ilsh)
		| Ash -> INTOP(iash)
		| Ldw -> MEMOP(register_set a (read_word (Int32.add (register_get b) c)))
		| Ldb -> MEMOP(register_set a (read_byte (Int32.add (register_get b) c)))
		| Stw -> MEMOP(write_word (Int32.add (register_get b) c) (register_get a))
		| Stb -> MEMOP(write_byte (Int32.add (register_get b) c) (register_get a))
		| Pop -> MEMOP(register_set a (read_word (register_get b));register_set b (Int32.add (register_get b) c))
		| Psh -> MEMOP(register_set b (Int32.sub (register_get b) c);write_word (register_get b) (register_get a))
		| Beq -> TESTOP((if int32_compare (register_get a) 0l = 0 then c else Int32.one))
		| Bne -> TESTOP((if int32_compare (register_get a) 0l <> 0 then c else Int32.one))
		| Blt -> TESTOP((if int32_compare (register_get a) 0l < 0 then c else Int32.one))
		| Bge -> TESTOP((if int32_compare (register_get a) 0l >= 0 then c else Int32.one))
		| Bgt -> TESTOP((if int32_compare (register_get a) 0l > 0 then c else Int32.one))
		| Ble -> TESTOP((if int32_compare (register_get a) 0l <= 0 then c else Int32.one))
		| Chk ->
		    (match mode with
		       | R ->
			   (function n ->
			      let c = Int32.logand n MASK_REG in
			      let n = Int32.shift_right_logical n 21 in
			      let a = Int32.logand n MASK_REG in
			      let va = register_get a in
				if ((int32_compare va 0l) >= 0) && ((int32_compare va (register_get c)) < 0) then
				  INCRPC(4l)
				else
				  raise (Error(ChkExn)))
		       | I ->
			   (function n ->
			      let c = Int32.logand n MASK_IMM in
			      let c = Int32.shift_right (Int32.shift_left c 16) 16 in (* 16 = 32 - 16 *)
			      let n = Int32.shift_right_logical n 21 in
			      let a = Int32.logand n MASK_REG in
			      let va = register_get a in
				if ((int32_compare va 0l) >= 0) && ((int32_compare va c) < 0) then
				  INCRPC(4l)
				else
				  raise (Error(ChkExn)))
		       | IU ->
			   (function n ->
			      let c = Int32.logand n MASK_IMM in
			      let n = Int32.shift_right_logical n 21 in
			      let a = Int32.logand n MASK_REG in
			      let va = register_get a in
				if ((int32_compare va 0l) >= 0) && ((int32_compare va c) < 0) then
				  INCRPC(4l)
				else
				  raise (Error(ChkExn)))
		       | Rel | Abs | Other -> assert false)
		| Bsr ->
		    (fun n ->
		       let c = Int32.logand n MASK_REL in
		       let c = Int32.shift_right (Int32.shift_left c 11) 11 in (* 11 = 32 - 21 *)
			 register_set 31l (Int32.add (!pc) 4l);
			 INCRPC(Int32.mul c 4l))
		| Jsr ->
		    (fun n ->
		       register_set 31l (Int32.add (!pc) 4l);
		       pc := Int32.mul (Int32.logand MASK_ABS n) 4l)
		| Ret ->
		    (fun n ->
		       let a = Int32.logand (Int32.shift_right_logical n 21) MASK_REG in
			 if int32_compare 0l a = 0 then raise (Error(Syscall(0l,0l,Risc.int_of_syscall Risc.Sys_exit)))
			 else pc := register_get a)
		| Break -> (fun _ -> raise (Error(BrkExn)))
		| Sys ->
		    (fun n ->
		       let c = Int32.logand n MASK_IMM in
		       let n = Int32.shift_right_logical n 16 in
		       let b = Int32.logand n MASK_REG in
		       let n = Int32.shift_right_logical n 5 in
		       let a = Int32.logand n MASK_REG in
			 raise (Error(Syscall(a,b,Int32.to_int c))))
	      with Not_found -> ()
	done;
	ops

    let reset () =
      for i = 0 to mem_size - 1 do
	memory.{i} <- 0l
      done;
      for i = 0 to 31 do
	register_set (Int32.of_int i) 0l;
      done;
      setPC 0l;
      Code.code#iter (fun i instr ->
			memory_set (Int32.of_int i) (Codec.code_instruction instr))

    let _ = reset ()

    let verbose = false

    exception Found of Int32.t

    let gc_init,gc_alloc =
      let align n = Int32.logand n 0xfffffffcl in
      let round n = align (Int32.add n 3l) in
      let hp_address = ref 0l
      and hp_size = ref 0l
      and hp_end = ref 0l
      and sp = ref 0l in
      let alive_cells = ref Gcmap.empty
      and dead_cells = ref Gcmap.empty
      and stack = Stack.create () in
      let new_cell sz b = { Gcmap.size = sz; Gcmap.live = b } in
      let dump_cells cells =
	Gcmap.iter (fun addr c ->
		      prerr_string "cell: ";
		      prerr_string (Int32.to_string addr);
		      prerr_string " size: ";
		      prerr_string (Int32.to_string c.Gcmap.size);
		      prerr_newline()) cells
      in
      let _dump () =
	prerr_string "alive cells\n";
	dump_cells !alive_cells;
	prerr_string "dead cells\n";
	dump_cells !dead_cells
      in
      let init hp sz reg =
	if (int32_compare hp 0l < 0) || (int32_compare hp mem_size_int32 >= 0) then
	  failwith ("out of bounds heap start: "^(Int32.to_string hp))
	else if (int32_compare (Int32.add hp sz) mem_size_int32 > 0) then
	  failwith ("out of bounds heap end: "^(Int32.to_string (Int32.add hp sz)))
	else if (int32_compare sz 0l < 0) then
	  failwith ("negative heap size: "^(Int32.to_string sz));
	let sz =
	  if int32_compare sz 0l = 0 then mem_size_int32
	  else Int32.add sz hp
	in
	let hp = round hp in
	let sz = min sz mem_size_int32 in
	let sz = max 0l (Int32.sub sz hp) in
	let sz = align sz in
	  hp_address := hp;
	  hp_size := sz;
	  hp_end := Int32.add !hp_address !hp_size;
	  sp := reg;
	  if verbose then
	    begin
	      prerr_string "[GC]";
	      prerr_string "heap address = ";prerr_string (Int32.to_string !hp_address);prerr_string ", ";
	      prerr_string "heap size = ";prerr_string (Int32.to_string !hp_size);prerr_string " bytes, ";
	      if(int32_compare !sp 0l = 0) then prerr_string "no stack pointer"
	      else (prerr_string "stack pointer = ";prerr_string (Int32.to_string !sp));
	      prerr_newline()
	    end;
	  alive_cells := Gcmap.empty;
	  dead_cells := Gcmap.add !hp_address (new_cell !hp_size false) (Gcmap.empty)
      in
      let lock sz =
	try
	  Gcmap.iter (fun addr c ->
			if int32_compare c.Gcmap.size sz >= 0 then
			  if int32_compare c.Gcmap.size sz = 0 then
			    begin
			      c.Gcmap.live <- false;
			      dead_cells := Gcmap.remove addr !dead_cells;
			      alive_cells := Gcmap.add addr c !alive_cells;
			      raise (Found(addr))
			    end
			  else
			    begin
			      c.Gcmap.size <- Int32.sub c.Gcmap.size sz;
			      dead_cells := Gcmap.add (Int32.add addr sz) c (Gcmap.remove addr !dead_cells);
			      alive_cells := Gcmap.add addr (new_cell sz true) !alive_cells;
			      raise (Found(addr))
			    end) !dead_cells;
	  if verbose then prerr_string "[GC]no cell allocated\n";
	  None
	with
	    Found(addr) ->
	      if verbose then
		begin
		  prerr_string "[GC]";
		  prerr_string "cell allocated: ";
		  prerr_string (Int32.to_string addr);
		  prerr_string " of size ";
		  prerr_string (Int32.to_string sz);
		  prerr_newline()
		end;
	      Some(addr)
      in
      let mark addr =
	try
	  let c = Gcmap.find addr !alive_cells in
	    if not (c.Gcmap.live) then
	      begin
		c.Gcmap.live <- true;
		Stack.push (addr,c) stack
	      end
	with Not_found -> ()
      and add_dead addr c =
	let addr2 = Int32.add addr c.Gcmap.size in
	  dead_cells := Gcmap.add_or_join addr addr2 c !dead_cells
      in
      let free () =
	let usage1 = ref 0l in
	  Gcmap.iter (fun _addr c ->
			c.Gcmap.live <- false;
			usage1 := Int32.add (!usage1) c.Gcmap.size) !alive_cells;
	  let stk_address =
	    if int32_compare !sp 0l = 0 then (Int32.add !hp_address !hp_size)
	    else register_get !sp
	  in
	  let stk_address = align stk_address in
	    if int32_compare stk_address !hp_end < 0 then
	      failwith "stack overwrote heap";
	    for i = 0 to 31 do
	      mark (register_get (Int32.of_int i))
	    done;
	      let i = ref Int32.zero in
		while int32_compare !i !hp_address < 0 do
		  mark (read_word !i);
		  i := Int32.add (!i) 4l
		done;
		i := stk_address;
		while int32_compare !i mem_size_int32 < 0 do
		  mark (read_word !i);
		  i := Int32.add (!i) 4l
		done;
		while not (Stack.is_empty stack) do
		  let (address,c) = Stack.pop stack in
		  let end_of_cell = Int32.add address c.Gcmap.size in
		    i := address;
		    while int32_compare !i end_of_cell < 0 do
		      mark (read_word !i);
		      i := Int32.add (!i) 4l
		    done
		done;
		let usage2 = ref 0l in
		  Gcmap.iter (fun addr c ->
				if c.Gcmap.live then
				  usage2 := Int32.add (!usage2) c.Gcmap.size
				else
				  begin
				    alive_cells := Gcmap.remove addr !alive_cells;
				    add_dead addr c
				  end)
		    !alive_cells;
		  if verbose then
		    begin
		      prerr_string "[GC]";
		      prerr_string (Int32.to_string (!usage1));
		      prerr_string " bytes -> ";
		      prerr_string (Int32.to_string (!usage2));
		      prerr_string " bytes";
		      prerr_newline()
		    end
      in
      let alloc sz =
	if (int32_compare sz 0l < 0) then failwith ("negative block size: "^(Int32.to_string sz));
	let sz = max 4l (round sz) in
	  match lock sz with
	    | Some(addr) -> addr
	    | None ->
		begin
		  free ();
		  match lock sz with
		    | Some(addr) -> addr
		    | None -> failwith ("could not allocate block of "^(Int32.to_string sz)^" bytes")
		end
      in init,alloc

    let tick () =
      DEBUG(prerr_string "PC: ";prerr_string (Int32.to_string (!pc));prerr_newline();)
	try
	  let n = read_word (!pc) in
	  let opcode = (Int32.to_int (Int32.shift_right_logical n 26)) land 0x3f in
	    get_op_table.(opcode) (n)
	with Error(Syscall(a,b,c)) ->
	  (match Risc.syscall_of_int c with
	     | Some(syscall) ->
		 (match syscall with
		    | Risc.Sys_exit -> raise (Error(Exit(register_get a)))
		    | Risc.Sys_io_wr_chr ->
			Pervasives.output_char stdout (Char.chr ((Int32.to_int (register_get a)) land 0xff));
		    | Risc.Sys_io_wr_int ->
			Pervasives.output_string stdout (Int32.to_string (register_get a))
		    | Risc.Sys_io_flush ->
			Pervasives.flush stdout
		    | Risc.Sys_io_rd_chr ->
			let n =
			  try Pervasives.input_byte stdin
			  with End_of_file -> -1
			in
			  register_set a (Int32.of_int n)
		    | Risc.Sys_io_rd_int ->
			register_set a (Int32.of_string (Pervasives.input_line stdin));
		    | Risc.Sys_get_total_mem_size ->
			register_set a mem_size_int32
		    | Risc.Sys_gc_init ->
			let ra = register_get a
			and rb = register_get b in
			let sz = Int32.shift_left (Int32.logand rb MASK_SZ) 2
			and sp = Int32.shift_right_logical rb 27 in
			  gc_init ra sz sp
		    | Risc.Sys_gc_alloc ->
			let sz = register_get b in
			  register_set a (gc_alloc sz)
		 );
		 INCRPC(4l)
	     | None -> raise (Error(Illegal)))


    let exec () =
      while true do
	tick ()
      done
  end
