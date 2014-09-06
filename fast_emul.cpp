(*

#define DEBUG(e) 

#define INCRPC(i) pc := Int32.add (i) (!pc)

#define INTOP(op) \
  (match mode with | R -> (function n -> \
  let c = Int32.logand n mask_reg in \
  let n = Int32.shift_right_logical n 16 in \
  let b = Int32.logand n mask_reg in \
  let n = Int32.shift_right_logical n 5 in \
  let a = Int32.logand n mask_reg in \
  register_set a (op (register_get b) (register_get c)); \
  INCRPC(four)) \
  | I -> \
  (function n -> \
  let c = Int32.logand n mask_imm in \
  let c = Int32.shift_right (Int32.shift_left c 16) 16 in (* 16 = 32 - 16 *) \
  let n = Int32.shift_right_logical n 16 in \
  let b = Int32.logand n mask_reg in \
  let n = Int32.shift_right_logical n 5 in \
  let a = Int32.logand n mask_reg in \
  register_set a (op (register_get b) c); \
  INCRPC(four)) \
  | IU -> \
  (function n -> \
  let c = Int32.logand n mask_imm in \
  let n = Int32.shift_right_logical n 16 in \
  let b = Int32.logand n mask_reg in \
  let n = Int32.shift_right_logical n 5 in \
  let a = Int32.logand n mask_reg in \
  register_set a (op (register_get b) c); \
  INCRPC(four)))

#define MEMOP(op) \
  (fun n -> \
  let c = Int32.logand mask_imm n in \
  let c = Int32.shift_right (Int32.shift_left c 16) 16 in (* 16 = 32 - 16 *) \
  let n = Int32.shift_right_logical n 16 in \
  let b = Int32.logand mask_reg n in \
  let n = Int32.shift_right_logical n 5 in \
  let a = Int32.logand mask_reg n in \
  op; \
  INCRPC(four)) 

#define TESTOP(op) \
  (fun n -> \
  let c = Int32.logand n mask_rel in \
  let c = Int32.shift_right (Int32.shift_left c 11) 11 in (* 11 = 32 - 21 *) \
  let n = Int32.shift_right_logical n 21 in \
  let a = Int32.logand n mask_reg in \
  INCRPC(Int32.mul op four))

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

    val register_get : Int32.t -> Int32.t
    val register_set : Int32.t -> Int32.t -> unit
    val read_word : Int32.t -> Int32.t
    val write_word : Int32.t -> Int32.t -> unit
    val getPC : unit -> Int32.t
    val setPC : Int32.t -> unit
    val exec : unit -> unit
  end

module Make(Code:Code) : Emulator = 
  struct
    type error = Illegal | BrkExn | ChkExn | Exit of Int32.t | Syscall of Int32.t * Int32.t * int 

    let int32_compare a b = Int32.to_int (Int32.sub (Int32.sub a b) (Int32.sub b a))

    let four = Int32.of_int 4
    let thirty_one = Int32.of_int 31
      
    exception Error of error

    let hex_string n =
      let res = ref "" in
	for i = 7 downto 0 do
	  let v = Int32.to_int (Int32.logand (Int32.shift_right_logical n (4*i)) (Int32.of_int 0xf)) in
	    if v < 10 then 
	      res := (!res)^(String.make 1 (Char.chr (48+v)))
	    else 
	      res := (!res)^(String.make 1 (Char.chr (65+v-10)))
	done;
	!res

    let pc = ref Int32.zero
	       
    let getPC () = !pc
    let setPC v = pc := v

    let registers = Array.create 32 Int32.zero
		      
    let register_get i = 
      DEBUG(prerr_string "getting register ";prerr_string (Int32.to_string i);prerr_newline();)
      registers.(Int32.to_int i)
			   
    let register_set i v =
      DEBUG(prerr_string "setting register ";prerr_string (Int32.to_string i);prerr_string " to value ";prerr_string (Int32.to_string v);prerr_newline();)
    let i = Int32.to_int i in
      if i > 0 then registers.(i) <- v

    let mem_size = Code.mem_size

    let mem_size_int32 = Int32.of_int mem_size
		     
    let memory =
      let res = Array1.create int32 c_layout mem_size in
	for i = 0 to mem_size - 1 do
	  res.{i} <- Int32.zero
	done;
	res
	  
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
      let mask = [|Int32.zero;Int32.zero;Int32.zero;Int32.zero|] in
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
      let ops = Array.create size (fun n -> raise (Error(Illegal))) in
      let mask_reg = Int32.of_int 0x1f 
      and mask_imm = Int32.of_int 0xffff 
      and mask_rel = Int32.of_int 0x1fffff
      and mask_abs = Int32.of_int 0x3ffffff in
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
		| Beq -> TESTOP((if int32_compare (register_get a) Int32.zero = 0 then c else Int32.one))
		| Bne -> TESTOP((if int32_compare (register_get a) Int32.zero <> 0 then c else Int32.one))
		| Blt -> TESTOP((if int32_compare (register_get a) Int32.zero < 0 then c else Int32.one))
		| Bge -> TESTOP((if int32_compare (register_get a) Int32.zero >= 0 then c else Int32.one))
		| Bgt -> TESTOP((if int32_compare (register_get a) Int32.zero > 0 then c else Int32.one))
		| Ble -> TESTOP((if int32_compare (register_get a) Int32.zero <= 0 then c else Int32.one))
		| Chk -> 
		    (match mode with
		       | R ->
			   (function n ->
			      let c = Int32.logand n mask_reg in
			      let n = Int32.shift_right_logical n 21 in
			      let a = Int32.logand n mask_reg in
			      let va = register_get a in
				if ((int32_compare va Int32.zero) >= 0) && ((int32_compare va (register_get c)) < 0) then
				  INCRPC(four)
				else
				  raise (Error(ChkExn)))
		       | I ->
			   (function n ->
			      let c = Int32.logand n mask_imm in
			      let c = Int32.shift_right (Int32.shift_left c 16) 16 in (* 16 = 32 - 16 *)
			      let n = Int32.shift_right_logical n 21 in
			      let a = Int32.logand n mask_reg in
			      let va = register_get a in
				if ((int32_compare va Int32.zero) >= 0) && ((int32_compare va c) < 0) then
				  INCRPC(four)
				else
				  raise (Error(ChkExn)))
		       | IU ->
			   (function n ->
			      let c = Int32.logand n mask_imm in
			      let n = Int32.shift_right_logical n 21 in
			      let a = Int32.logand n mask_reg in
			      let va = register_get a in
				if ((int32_compare va Int32.zero) >= 0) && ((int32_compare va c) < 0) then
				  INCRPC(four)
				else
				  raise (Error(ChkExn))))
		| Bsr ->
		    (fun n ->
		       let c = Int32.logand n mask_rel in
		       let c = Int32.shift_right (Int32.shift_left c 11) 11 in (* 11 = 32 - 21 *)
			 register_set thirty_one (Int32.add (!pc) four);
			 INCRPC(Int32.mul c four))
		| Jsr -> 
		    (fun n ->
		       register_set thirty_one (Int32.add (!pc) four);
		       pc := Int32.mul (Int32.logand mask_abs n) four)
		| Ret -> 
		    (fun n ->
		       let a = Int32.logand (Int32.shift_right_logical n 21) mask_reg in
			 if int32_compare Int32.zero a = 0 then raise (Error(Syscall(Int32.zero,Int32.zero,Risc.int_of_syscall Risc.Sys_exit)))
			 else pc := register_get a)
		| Break -> (fun n -> raise (Error(BrkExn)))
		| Sys ->
		    (fun n ->
		       let c = Int32.logand n mask_imm in
		       let n = Int32.shift_right_logical n 16 in
		       let b = Int32.logand n mask_reg in
		       let n = Int32.shift_right_logical n 5 in
		       let a = Int32.logand n mask_reg in
			 raise (Error(Syscall(a,b,Int32.to_int c))))
	      with Not_found -> ()
	done;
	ops

    let _ =
      Code.code#iter (fun i instr ->
			memory_set (Int32.of_int i) (Codec.code_instruction instr))

    let verbose = false

    let gc_init,gc_alloc =
      let align n = n land 0x7ffffffc in
      let round n = align (n + 3) in
      let hp_address = ref 0 and hp_size = ref 0 and sp = ref 0 in
      let init hp sz reg =
	let hp = Int32.to_int hp and sz = Int32.to_int sz and reg = Int32.to_int reg in
	if (hp < 0) || (hp >= mem_size) then
	  failwith ("out of bounds heap start: "^(string_of_int hp))
	else if (hp + sz - 1 >= mem_size) then
	  failwith ("out of bounds heap end: "^(string_of_int (hp + sz - 1)))
	else if (sz < 0) then
	  failwith ("negative heap size: "^(string_of_int sz));
	let sz = if sz = 0 then mem_size else sz + hp in
	let hp = round hp in
	let sz = min sz mem_size in
	let sz = max 0 (sz - hp) in
	let sz = align sz in
	  hp_address := hp;
	  hp_size := sz;
	  sp := reg;
	  if verbose then
	    begin
	      prerr_string "[GC]";
	      prerr_string "heap address = ";prerr_int (!hp_address);prerr_string ", ";
	      prerr_string "heap size = ";prerr_int (!hp_size);prerr_string " bytes, ";
	      if(!sp = 0) then prerr_string "no stack pointer"
	      else (prerr_string "stack pointer = ";prerr_int (!sp));
	      prerr_newline()
	    end
      and alloc sz =
	let sz = Int32.to_int sz in
	if (sz < 0) then failwith ("negative block size: "^(string_of_int sz));
	let sz = max 4 (round sz) in
	let addr = !hp_address in
	  hp_address := !hp_address + sz;
	  Int32.of_int addr
      in init,alloc

    let exec () = 
      let mask_sz = Int32.of_int 0x1ffffff in
	while true do
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
			  let sz = Int32.shift_left (Int32.logand rb mask_sz) 2
			  and sp = Int32.shift_right_logical rb 27 in
			    gc_init ra sz sp
		      | Risc.Sys_gc_alloc -> 
			  let sz = register_get b in
			    register_set a (gc_alloc sz)
		      | _ -> failwith "syscall not yet implemented"
		   );
		   INCRPC(four)
	       | None -> raise (Error(Illegal)))
	done
  end
