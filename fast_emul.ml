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

    let four = Int32.of_int 4
    let thirty_one = Int32.of_int 31
	       
    let getPC () = !pc
    let setPC v = pc := v

    let registers = Array.create 32 Int32.zero
		      
    let register_get i = 
      (* prerr_string "getting register ";prerr_string (Int32.to_string i);prerr_newline(); *)
      registers.(Int32.to_int i)
			   
    let register_set i v =
     (* prerr_string "setting register ";prerr_string (Int32.to_string i);prerr_string " to value ";prerr_string (Int32.to_string v);prerr_newline(); *)
      if Int32.compare Int32.zero i <> 0 then
	registers.(Int32.to_int i) <- v
	  
    let mem_size = Code.mem_size
		     
    let memory =
      let res = Array1.create int32 c_layout mem_size in
	for i = 0 to mem_size - 1 do
	  res.{i} <- Int32.zero
	done;
	res
	  
    let memory_get i = memory.{Int32.to_int i}
			 
    let memory_set i v = memory.{Int32.to_int i} <- v
			   
    let read_word addr =
      (* prerr_string "reading word at ";prerr_string (Int32.to_string addr);prerr_newline(); *)
      memory_get (Int32.shift_right addr 2)
	
    let write_word addr v =
      (* prerr_string "writting word at ";prerr_string (Int32.to_string addr);prerr_string ": ";prerr_string (Int32.to_string v);prerr_newline(); *)
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
	
    let exec_op =
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
      and mask_abs = Int32.of_int 0x3ffffff
      and mask_sign_imm = Int32.of_int 0x8000 
      and ext_sign_imm = Int32.shift_left (Int32.of_int 0xffff) 16 
      and mask_sign_rel = Int32.of_int 0x100000 
      and ext_sign_rel = Int32.shift_left (Int32.of_int 0x7ff) 21 in
      let iadd a b = Int32.add a b 
      and isub a b = Int32.sub a b 
      and imul a b = Int32.mul a b
      and idiv a b = Int32.div a b
      and imod a b = Int32.rem a b
      and icmp a b = Int32.of_int (Int32.compare a b)
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
      let int_op iop = function
	| R ->
	    (function n ->
	       let c = Int32.logand n mask_reg in
	       let n = Int32.shift_right_logical n 16 in
	       let b = Int32.logand n mask_reg in
	       let n = Int32.shift_right_logical n 5 in
	       let a = Int32.logand n mask_reg in
		 register_set a (iop (register_get b) (register_get c));
		 pc := Int32.add four (!pc)
	    )
	| I ->
	    (function n ->
	       let c = Int32.logand n mask_imm in
	       let c = if Int32.compare (Int32.logand c mask_sign_imm) Int32.zero <> 0 then Int32.logor c ext_sign_imm else c in
	       let n = Int32.shift_right_logical n 16 in
	       let b = Int32.logand n mask_reg in
	       let n = Int32.shift_right_logical n 5 in
	       let a = Int32.logand n mask_reg in
		 register_set a (iop (register_get b) c);
		 pc := Int32.add four (!pc))
	| IU ->
	    (function n ->
	       let c = Int32.logand n mask_imm in
	       let n = Int32.shift_right_logical n 16 in
	       let b = Int32.logand n mask_reg in
	       let n = Int32.shift_right_logical n 5 in
	       let a = Int32.logand n mask_reg in
		 register_set a (iop (register_get b) c);
		 pc := Int32.add four (!pc))
      in
      let test_op iop =
	(fun n ->
	   let c = Int32.logand n mask_rel in
	   let c = if Int32.compare (Int32.logand c mask_sign_rel) Int32.zero <> 0 then Int32.logor c ext_sign_rel else c in
	   let n = Int32.shift_right_logical n 21 in
	   let a = Int32.logand mask_reg n in
	     pc := Int32.add (Int32.mul four (iop (register_get a) c)) (!pc))
      in
	for i = 0 to size - 1 do
	  try
	    let (_,op,mode) = List.find (fun (x,_,_) -> x = i) instrs in
	      ops.(i) <-
	      match op with
		| Add -> int_op iadd mode
		| Sub -> int_op isub mode
		| Mul -> int_op imul mode
		| Div -> int_op idiv mode
		| Cmp -> int_op icmp mode
		| Mod -> int_op imod mode
		| And -> int_op iand mode
		| Or -> int_op ior mode
		| Xor -> int_op ixor mode
		| Bic -> int_op ibic mode
		| Lsh -> int_op ilsh mode
		| Ash -> int_op iash mode
		| Ldw -> 
		    (function n ->
		       let c = Int32.logand mask_imm n in
		       let c = if Int32.compare Int32.zero (Int32.logand mask_sign_imm c) <> 0 then Int32.logor ext_sign_imm c else c in
		       let n = Int32.shift_right_logical n 16 in
		       let b = Int32.logand mask_reg n in
		       let n = Int32.shift_right_logical n 5 in
		       let a = Int32.logand mask_reg n in
			 register_set a (read_word (Int32.add (register_get b) c));
			 pc := Int32.add four (!pc)
		    )
		| Ldb -> 
		    (function n ->
		       let c = Int32.logand mask_imm n in
		       let c = if Int32.compare Int32.zero (Int32.logand mask_sign_imm c) <> 0 then Int32.logor ext_sign_imm c else c in
		       let n = Int32.shift_right_logical n 16 in
		       let b = Int32.logand mask_reg n in
		       let n = Int32.shift_right_logical n 5 in
		       let a = Int32.logand mask_reg n in
			 register_set a (read_byte (Int32.add (register_get b) c));
			 pc := Int32.add four (!pc))
		| Stw -> 
		    (function n ->
		       let c = Int32.logand mask_imm n in
		       let c = if Int32.compare Int32.zero (Int32.logand mask_sign_imm c) <> 0 then Int32.logor ext_sign_imm c else c in
		       let n = Int32.shift_right_logical n 16 in
		       let b = Int32.logand mask_reg n in
		       let n = Int32.shift_right_logical n 5 in
		       let a = Int32.logand mask_reg n in
			 write_word (Int32.add (register_get b) c) (register_get a);
			 pc := Int32.add four (!pc))
		| Stb -> 
		    (function n ->
		       let c = Int32.logand mask_imm n in
		       let c = if Int32.compare Int32.zero (Int32.logand mask_sign_imm c) <> 0 then Int32.logor ext_sign_imm c else c in
		       let n = Int32.shift_right_logical n 16 in
		       let b = Int32.logand mask_reg n in
		       let n = Int32.shift_right_logical n 5 in
		       let a = Int32.logand mask_reg n in
			 write_byte (Int32.add (register_get b) c) (register_get a);
			 pc := Int32.add four (!pc))
		| Pop ->
		    (function n ->
		       let c = Int32.logand mask_imm n in
		       let c = if Int32.compare Int32.zero (Int32.logand mask_sign_imm c) <> 0 then Int32.logor ext_sign_imm c else c in
		       let n = Int32.shift_right_logical n 16 in
		       let b = Int32.logand mask_reg n in
		       let n = Int32.shift_right_logical n 5 in
		       let a = Int32.logand mask_reg n in
			 register_set a (read_word (register_get b));
			 register_set b (Int32.add (register_get b) c);
			 pc := Int32.add four (!pc))
		| Psh -> 
		    (function n ->
		       let c = Int32.logand mask_imm n in
		       let c = if Int32.compare Int32.zero (Int32.logand mask_sign_imm c) <> 0 then Int32.logor ext_sign_imm c else c in
		       let n = Int32.shift_right_logical n 16 in
		       let b = Int32.logand mask_reg n in
		       let n = Int32.shift_right_logical n 5 in
		       let a = Int32.logand mask_reg n in
			 register_set b (Int32.sub (register_get b) c);
			 write_word (register_get b) (register_get a);
			 pc := Int32.add four (!pc))
		| Beq -> test_op (fun v dep -> if Int32.compare v Int32.zero = 0 then dep else Int32.one)
		| Bne -> test_op (fun v dep -> if Int32.compare v Int32.zero <> 0 then dep else Int32.one)
		| Blt -> test_op (fun v dep -> if Int32.compare v Int32.zero < 0 then dep else Int32.one)
		| Bge -> test_op (fun v dep -> if Int32.compare v Int32.zero >= 0 then dep else Int32.one)
		| Bgt -> test_op (fun v dep -> if Int32.compare v Int32.zero > 0 then dep else Int32.one)
		| Ble -> test_op (fun v dep -> if Int32.compare v Int32.zero <= 0 then dep else Int32.one)
		| Chk -> 
		    (match mode with
		       | R ->
			   (function n ->
			      let c = Int32.logand mask_reg n in
			      let n = Int32.shift_right_logical n 21 in
			      let a = Int32.logand mask_reg n in
			      let va = register_get a in
				if ((Int32.compare va Int32.zero) >= 0) && ((Int32.compare va (register_get c)) < 0) then
				  pc := Int32.add four (!pc)
				else
				  raise (Error(ChkExn)))
		       | I ->
			   (function n ->
			      let c = Int32.logand mask_imm n in
			      let c = if Int32.compare Int32.zero (Int32.logand mask_sign_imm c) <> 0 then Int32.logor ext_sign_imm c else c in
			      let n = Int32.shift_right_logical n 21 in
			      let a = Int32.logand mask_reg n in
			      let va = register_get a in
				if ((Int32.compare va Int32.zero) >= 0) && ((Int32.compare va c) < 0) then
				  pc := Int32.add four (!pc)
				else
				  raise (Error(ChkExn)))
		       | IU ->
			   (function n ->
			      let c = Int32.logand mask_imm n in
			      let n = Int32.shift_right_logical n 21 in
			      let a = Int32.logand mask_reg n in
			      let va = register_get a in
				if ((Int32.compare va Int32.zero) >= 0) && ((Int32.compare va c) < 0) then
				  pc := Int32.add four (!pc)
				else
				  raise (Error(ChkExn))))
		| Bsr ->
		    (fun n ->
		       register_set thirty_one (Int32.add (!pc) four);
		       pc := Int32.add (!pc) (Int32.mul four (Int32.logand mask_rel n)))
		| Jsr -> 
		    (fun n ->
		       register_set thirty_one (Int32.add (!pc) four);
		       pc := Int32.mul four (Int32.logand mask_abs n))
		| Ret -> 
		    (fun n ->
		       let a = Int32.logand mask_reg (Int32.shift_right_logical n 21) in
			 if Int32.compare Int32.zero a = 0 then raise (Error(Syscall(Int32.zero,Int32.zero,Risc.int_of_syscall Risc.Sys_exit)))
			 else pc := register_get a)
		| Break -> (fun n -> raise (Error(BrkExn)))
		| Sys ->
		    (fun n ->
		       let c = Int32.logand mask_imm n in
		       let n = Int32.shift_right_logical n 16 in
		       let b = Int32.logand mask_reg n in
		       let n = Int32.shift_right_logical n 5 in
		       let a = Int32.logand mask_reg n in
			 raise (Error(Syscall(a,b,Int32.to_int c))))
	      with Not_found -> ()
	done;
	fun n -> 
	  let opcode = (Int32.to_int (Int32.shift_right_logical n 26)) land 0x3f in
	    (* prerr_string "opcode: ";prerr_int opcode;prerr_newline(); *)
	    ops.(opcode) n

    let _ =
      Code.code#iter (fun i instr ->
			memory_set (Int32.of_int i) (Codec.code_instruction instr))

    let exec () = 
      while true do
	(* prerr_string "PC: ";prerr_string (Int32.to_string (!pc));prerr_newline(); *)
	try
	  exec_op (read_word (!pc))
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
			register_set a (Int32.of_int mem_size)
		    | Risc.Sys_gc_init -> failwith "gc_init"
		    | Risc.Sys_gc_alloc -> failwith "gc_init"
		    | _ -> ()
		 );
		 pc := Int32.add four (!pc)
	     | None -> raise (Error(Illegal)))
      done
end
