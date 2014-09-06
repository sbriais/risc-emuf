open Bigarray

module type Code = 
  sig
    val mem_size : int
    val code : Risc.code_generator
  end
	
module type Emulator =
  sig
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
    let pc = ref Int32.zero
	       
    let getPC () = !pc
    let setPC v = pc := v

    let registers = Array.create 32 Int32.zero
		      
    let register_get i = registers.(Int32.to_int i)
			   
    let register_set i v =
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
      memory_get (Int32.shift_right addr 2)
	
    let write_word addr v =
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
	      
    type error = Illegal | Syscall of int
      
    exception Error of error
      
    type instruction = 
      | Add | Sub | Mul | Div | Cmp | Mod
      | And | Or | Xor | Bic
      | Lsh | Ash
      | Ldw | Ldb | Stw | Stb | Pop | Psh
      | Beq | Bne | Blt | Bge | Bgt | Ble
      | Chk 
      | Bsr | Jsr | Ret
      | Break | Syscall 
	    
    type mode = R | I | IU | Rel | Abs | Sys | N | R1
	
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
		 (List.map (fun (x,y) -> (x,y,I)) sh)
	in
	let chk = [14,Chk,R;30,Chk,I;39,Chk,IU] in
	let mem = [32,Ldw;33,Ldb;34,Pop;36,Stw;37,Stb;38,Psh] in
	let mem = List.map (fun (x,y) -> (x,y,I)) mem in
	let test = [40,Beq;41,Bne;42,Blt;43,Bge;44,Ble;45,Bgt] in
	let test = List.map (fun (x,y) -> (x,y,Rel)) test in
	let bsr = [46,Bsr,Rel] and jsr = [48,Jsr,Abs] and ret = [49,Ret,R1] in
	let brk = [6,Break,N] and sysc = [7,Syscall,Sys] in
	  arith@log@sh@chk@mem@test@bsr@jsr@ret@brk@sysc
      in
      let size = 1 lsl 6 in
      let ops = Array.create size (fun n -> raise (Error(Illegal))) in
      let mask_reg = Int32.of_int 0x1f in
      let mask_imm = Int32.of_int 0xffff in
      let mask_sign = Int32.of_int 0x8000 in
      let ext_sign = Int32.shift_left (Int32.of_int 0xffff) 16 in
      let four = Int32.of_int 4 in
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
      let riiu iop = function
	| R ->
	    (function n ->
	       let c = Int32.logand mask_reg n in
	       let n = Int32.shift_right_logical n 21 in
	       let b = Int32.logand mask_reg n in
	       let n = Int32.shift_right_logical n 5 in
	       let a = Int32.logand mask_reg n in
		 register_set a (iop (register_get b) (register_get c));
		 pc := Int32.add four (!pc)
	    )
	| I ->
	    (function n ->
	       let c = Int32.logand mask_imm n in
	       let c = if Int32.compare Int32.zero (Int32.logand mask_sign c) <> 0 then Int32.logor ext_sign c else c in
	       let n = Int32.shift_right_logical n 21 in
	       let b = Int32.logand mask_reg n in
	       let n = Int32.shift_right_logical n 5 in
	       let a = Int32.logand mask_reg n in
		 register_set a (iop (register_get b) c);
		 pc := Int32.add four (!pc))
	| IU ->
	    (function n ->
	       let c = Int32.logand mask_imm n in
	       let n = Int32.shift_right_logical n 21 in
	       let b = Int32.logand mask_reg n in
	       let n = Int32.shift_right_logical n 5 in
	       let a = Int32.logand mask_reg n in
		 register_set a (iop (register_get b) c);
		 pc := Int32.add four (!pc))
      in
	for i = 0 to size - 1 do
	  try
	    let (_,op,mode) = List.find (fun (x,_,_) -> x = i) instrs in
	      ops.(i) <-
	      match op with
		| Add -> riiu iadd mode
		| Sub -> riiu isub mode
		| Mul -> riiu imul mode
		| Div -> riiu idiv mode
		| Cmp -> riiu icmp mode
		| Mod -> riiu imod mode
		| And -> riiu iand mode
		| Or -> riiu ior mode
		| Xor -> riiu ixor mode
		| Bic -> riiu ibic mode
		| Lsh -> riiu ilsh mode
		| Ash -> riiu iash mode
		| Ldw | Ldb | Stw | Stb | Pop | Psh
		| Beq | Bne | Blt | Bge | Bgt | Ble
		| Chk 
		| Bsr | Jsr | Ret
		| Break | Syscall -> raise Not_found
	      with Not_found -> ()
	done;
	ops

    let _ =
      Code.code#iter (fun i instr ->
			memory_set (Int32.of_int i) (Codec.code_instruction instr))

    let exec () = 
      while true do
	let n = read_word (!pc) in
	let opcode = (Int32.to_int (Int32.shift_right_logical n 26)) land 0x3f in
	  exec_op.(opcode) n
      done
end
