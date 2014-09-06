open Risc

exception WrongOpCode

let register c =
  if (0 <= c) && (c <= 31) then R(c)
  else raise WrongOpCode

let signed c =
  let n = Int32.of_int c in
  let n = Int32.shift_left n 16 in
  let n = Int32.shift_right n 16 in
  let c = Int32.to_int n in
    Signed(freeze c)

let unsigned c = 
  let n = Int32.of_int c in
  let n = Int32.shift_left n 16 in
  let n = Int32.shift_right_logical n 16 in
  let c = Int32.to_int n in
    Unsigned(freeze c)

let relative c =
  let n = Int32.of_int c in
  let n = Int32.shift_left n (32-21) in
  let n = Int32.shift_right n (32-21) in
  let c  = Int32.to_int n in
    Relative(freeze c)

let absolute c = Absolute(freeze c)

let case_ariiu_r c = AR(register c)

let case_ariiu_i c = AI(signed c)

let case_ariiu_iu c = AIU(unsigned c)

let case_bri_r c = BR(register c)

let case_bri_i c = BI(signed c)

let code_of_arith_op,arith_op_decode = 
  let assoc,i,iu = 
    [Add,0;
     Sub,1;
     Mul,2;
     Div,3;
     Mod,4;
     Cmp,5],16,54
  in
  let code op c =
    let (_,base) = List.find (fun (x,_) -> x = op) assoc
    in
      match c with
	  AR(_) -> base
	| AI(_) -> base + i
	| AIU(_) -> base + iu
  and decode n =
    try
      Some(fst (List.find (fun (_,x) -> x = n) assoc),case_ariiu_r)
    with
	Not_found ->
	  (try
	     Some(fst (List.find (fun (_,x) -> x + i = n) assoc),case_ariiu_i)
	   with
	       Not_found ->
		 (try
		    Some(fst (List.find (fun (_,x) -> x + iu = n) assoc),case_ariiu_i)
		  with
		      Not_found -> None))
  in code,decode

let code_of_log_op,log_op_decode = 
  let assoc,i,iu = 
    [Or,8;
     And,9;
     Bic,10;
     Xor,11],16,52
  in
  let code op c = 
    let (_,base) = List.find (fun (x,_) -> x = op) assoc
    in
      match c with
	  AR(_) -> base
	| AI(_) -> base + i
	| AIU(_) -> base + iu
  and decode n =
    try
      Some(fst (List.find (fun (_,x) -> x = n) assoc),case_ariiu_r)
    with
	Not_found ->
	  (try
	     Some(fst (List.find (fun (_,x) -> x + i = n) assoc),case_ariiu_i)
	   with
	       Not_found ->
		 (try
		    Some(fst (List.find (fun (_,x) -> x + iu = n) assoc),case_ariiu_iu)
		  with
		      Not_found -> None))
  in code,decode

let code_of_sh_op,sh_op_decode = 
  let assoc,i =
    [Lsh,12;
     Ash,13],16
  in
  let code op c =
    let (_,base) = List.find (fun (x,_) -> x = op) assoc
    in
      match c with
	  BR(_) -> base
	| BI(_) -> base + i
  and decode n =
    try
      Some(fst (List.find (fun (_,x) -> x = n) assoc),case_bri_r)
    with 
	Not_found ->
	  (try
	     Some(fst (List.find (fun (_,x) -> x + i = n) assoc),case_bri_i)
	   with
	       Not_found -> None)
  in code,decode

let code_of_chk,chk_decode = 
  let r,i,iu = 14,30,39
  in
  let code = function
      AR(_) -> r
    | AI(_) -> i
    | AIU(_) -> iu
  and decode n =
    if n = r then Some(case_ariiu_r)
    else if n = i then Some(case_ariiu_i)
    else if n = iu then Some(case_ariiu_iu)
    else None
  in code,decode

let code_of_mem_op,mem_op_decode = 
  let assoc =
    [Ldw,32;
     Ldb,33;
     Pop,34;
     Stw,36;
     Stb,37;
     Psh,38]
  in
  let code op =
    snd (List.find (fun (x,_) -> x = op) assoc)
  and decode n =
    try
      Some(fst (List.find (fun (_,x) -> x = n) assoc))
    with Not_found -> None
  in code,decode

let code_of_test_op,test_op_decode = 
  let assoc =
    [Beq,40;
     Bne,41;
     Blt,42;
     Bge,43;
     Ble,44;
     Bgt,45]
  in
  let code op = 
    snd (List.find (fun (x,_) -> x = op) assoc)
  and decode n =
    try
      Some(fst (List.find (fun (_,x) -> x = n) assoc))
    with Not_found -> None
  in code,decode

let code_of_bsr = 46

let code_of_jsr = 48

let code_of_ret = 49

let code_of_break = 6

let code_of_syscall = 7

let code_3 op a b c =
  let code = Int32.shift_left (Int32.of_int op) 5 in
  let code = Int32.shift_left (Int32.logor code (Int32.of_int a)) 5 in
  let code = Int32.shift_left (Int32.logor code (Int32.of_int b)) 16 in
    Int32.logor code (Int32.of_int c)

let decode_3 n =
  let c = Int32.to_int (Int32.logand n 0xffffl) in
  let n = Int32.shift_right_logical n 16 in
  let b = Int32.to_int (Int32.logand n 0x1fl) in
  let n = Int32.shift_right_logical n 5 in
  let a = Int32.to_int (Int32.logand n 0x1fl) in
    a,b,c

let code_2 op a c =
  let code = Int32.shift_left (Int32.of_int op) 5 in
  let code = Int32.shift_left (Int32.logor code (Int32.of_int a)) 21 in
    Int32.logor code (Int32.of_int c)

let decode_2 n =
  let c = Int32.to_int (Int32.logand n 0x1fffffl) in
  let n = Int32.shift_right_logical n 21 in
  let a = Int32.to_int (Int32.logand n 0x1fl) in
    a,c

let code_1_reg op a =
  let code = Int32.shift_left (Int32.of_int op) 5 in
    Int32.shift_left (Int32.logor code (Int32.of_int a)) 21

let code_1_imm op c =
  let code = Int32.shift_left (Int32.of_int op) 26 in
    Int32.logor code (Int32.of_int c)

let decode_1 n =
  Int32.to_int (Int32.logand n 0x3ffffffl)

let code_0 op =
  Int32.shift_left (Int32.of_int op) 26

let code_of_signed (Signed(f)) = (f ()) land 0xffff
let code_of_unsigned (Unsigned(f)) = (f ()) land 0xffff
let code_of_relative (Relative(f)) = (f ()) land 0x1fffff
let code_of_absolute (Absolute(f)) = (f ()) land 0x3ffffff

let code_of_ariiu = function
    AR(R(c)) -> c
  | AI(n) -> code_of_signed n
  | AIU(n) -> code_of_unsigned n

let code_of_bri = function
    BR(R(c)) -> c
  | BI(n) -> code_of_signed n

let code_instruction = function
  | IArith(op,R(a),R(b),c) ->
      let code = code_of_arith_op op c in
	code_3 code a b (code_of_ariiu c)
  | ILog(op,R(a),R(b),c) ->
      let code = code_of_log_op op c in
	code_3 code a b (code_of_ariiu c)
  | ISh(op,R(a),R(b),c) ->
      let code = code_of_sh_op op c in
	code_3 code a b (code_of_bri c)
  | IMem(op,R(a),R(b),n) ->
      let code = code_of_mem_op op in
	code_3 code a b (code_of_signed n)
  | ITest(op,R(a),c) ->
      let code = code_of_test_op op in
	code_2 code a (code_of_relative c)
  | Chk(R(a),c) ->
      let code = code_of_chk c in
	code_2 code a (code_of_ariiu c)
  | Bsr(c) ->
      let code = code_of_bsr in
	code_1_imm code (code_of_relative c)
  | Jsr(c) ->
      let code = code_of_jsr in
	code_1_imm code (code_of_absolute c)
  | Ret(R(a)) ->
      let code = code_of_ret in
	code_1_reg code a
  | Break ->
      let code = code_of_break in
	code_0 code
  | Syscall(R(a),R(b),syscall) ->
      let code = code_of_syscall in
      let c = int_of_syscall syscall in
	code_3 code a b c
  | Data(n) -> n ()

let decode_instruction n =
  let op = (Int32.to_int (Int32.shift_right_logical n 26)) land 0x3f in
    try
      match arith_op_decode op with
	  Some(op,third) -> 
	    let a,b,c = decode_3 n in
	      IArith(op,R(a),R(b),(third c))
	| None ->
	    (match log_op_decode op with
		 Some(op,third) -> 
		   let a,b,c = decode_3 n in
		     ILog(op,R(a),R(b),(third c))
	       | None -> 
		   (match sh_op_decode op with
			Some(op,third) -> 
			  let a,b,c = decode_3 n in
			    ISh(op,R(a),R(b),(third c))
		      | None ->
			(match mem_op_decode op with
			     Some(op) -> 
			       let a,b,c = decode_3 n in
				 IMem(op,R(a),R(b),signed c)
			   | None -> 
			       (match test_op_decode op with
				    Some(op) -> 
				      let a,c = decode_2 n in
					ITest(op,R(a),relative c)
				  | None -> 
				      (match chk_decode op with
					   Some(second) -> 
					     let a,c = decode_2 n in
					       Chk(R(a),(second c))
					 | None ->
					     if op = code_of_bsr then 
					       let c = decode_1 n in Bsr(relative c)
					     else if op = code_of_jsr then 
					       let c = decode_1 n in Jsr(absolute c)
					     else if op = code_of_ret then 
					       begin
						 let c = decode_1 n in
						 let a = (c lsr 21) land 0x1f in
						   Ret(R(a))
					       end
					     else if op = code_of_break then Break
					     else if op = code_of_syscall then 
					       begin
						 let a,b,c = decode_3 n in
						   match syscall_of_int c with
						       Some(syscall) -> Syscall(R(a),R(b),syscall)
						     | None -> raise WrongOpCode
					       end
					     else raise WrongOpCode)))))
      with WrongOpCode -> Data(freeze n)
