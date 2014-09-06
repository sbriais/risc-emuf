type register = R of int

type ic = Signed of (unit -> int)
type uc = Unsigned of (unit -> int)
type oc = Relative of (unit -> int)
type lc = Absolute of (unit -> int)

type a_riiu = AR of register | AI of ic | AIU of uc

type b_ri = BR of register | BI of ic

type arith_op = Add | Sub | Mul | Div | Cmp | Mod
type logical_op = And | Or | Xor | Bic
type logical_sh = Lsh | Ash
type mem_op = Ldw | Ldb | Stw | Stb | Pop | Psh
type test_op = Beq | Bne | Blt | Bge | Bgt | Ble

type syscall = 
  | Sys_io_rd_chr
  | Sys_io_rd_int
  | Sys_io_wr_chr
  | Sys_io_wr_int
  | Sys_gc_init 
  | Sys_gc_alloc
  | Sys_get_total_mem_size
  | Sys_io_flush
  | Sys_exit

type instruction = 
    IArith of arith_op * register * register * a_riiu
  | ILog of logical_op * register * register * a_riiu
  | ISh of logical_sh * register * register * b_ri
  | IMem of mem_op * register * register * ic
  | ITest of test_op * register * oc
  | Chk of register * a_riiu
  | Bsr of oc
  | Jsr of lc
  | Ret of register
  | Break
  | Syscall of register * register * syscall
  | Data of (unit -> Int32.t)

let freeze n = function () -> n

let string_of_ic (Signed(f)) = string_of_int (f ())
let string_of_uc (Unsigned(f)) = string_of_int (f ())
let string_of_oc (Relative(f)) = string_of_int (f ())
let string_of_lc (Absolute(f)) = string_of_int (f ())
let string_of_register (R(n)) = string_of_int n

let string_of_a a =
  match a with
      AR(reg) -> string_of_register reg
    | AI(i) -> string_of_ic i 
    | AIU(u) -> string_of_uc u

let string_of_b b =
  match b with
      BR(reg) -> string_of_register reg
    | BI(i) -> string_of_ic i 

let postfix_of_a = function
    AR(_) -> ""
  | AI(_) -> "I"
  | AIU(_) -> "IU"

let postfix_of_b = function
    BR(_) -> ""
  | BI(_) -> "I"

let int_of_syscall,syscall_of_int = 
  let assoc = 
    [Sys_io_rd_chr,1;
     Sys_io_rd_int,2;
     Sys_io_wr_chr,6;
     Sys_io_wr_int,7;
     Sys_gc_init,11;
     Sys_gc_alloc,12;
     Sys_get_total_mem_size,13;
     Sys_io_flush,15;
     Sys_exit,19]
  in
  let to_int sysc =
    snd (List.find (fun (x,_) -> x = sysc) assoc)
  and of_int n =
    try
      Some(fst (List.find (fun (_,x) -> x = n) assoc))
    with
	Not_found -> None
  in to_int,of_int

let string_of_arith = function
    Add -> "ADD"
  | Sub -> "SUB"
  | Mul -> "MUL"
  | Div -> "DIV"
  | Cmp -> "CMP"
  | Mod -> "MOD"

let string_of_log = function
    And -> "AND"
  | Or -> "OR"
  | Xor -> "XOR"
  | Bic -> "BIC"

let string_of_sh = function
    Lsh -> "LSH"
  | Ash -> "ASH"

let string_of_mem = function
    Ldw -> "LDW"
  | Ldb -> "LDB"
  | Stw -> "STW"
  | Stb -> "STB"
  | Pop -> "POP"
  | Psh -> "PSH"

let string_of_test = function
    Beq -> "BEQ"
  | Bne -> "BNE"
  | Blt -> "BLT"
  | Bge -> "BGE"
  | Bgt -> "BGT"
  | Ble -> "BLE"

let mnemo_of_instruction = function
    IArith(op,_,_,arg) -> (string_of_arith op)^(postfix_of_a arg)
  | ILog(op,_,_,arg) -> (string_of_log op)^(postfix_of_a arg)
  | ISh(op,_,_,arg) -> (string_of_sh op)^(postfix_of_b arg)
  | IMem(op,_,_,_) -> (string_of_mem op)
  | ITest(op,_,_) -> (string_of_test op)
  | Chk(_,arg) -> "CHK"^(postfix_of_a arg)
  | Bsr(_) -> "BSR"
  | Jsr(_) -> "JSR"
  | Ret(_) -> "RET"
  | Break -> "BREAK"
  | Syscall(_) -> "SYSCALL"
  | Data(_) -> "DW"

let string_of_instruction instr = 
  let sep = " " in
    (mnemo_of_instruction instr)^sep^(
      match instr with
	  IArith(_,a,b,c) 
	| ILog(_,a,b,c) -> (string_of_register a)^sep^(string_of_register b)^sep^(string_of_a c)
	| ISh(_,a,b,c) -> (string_of_register a)^sep^(string_of_register b)^sep^(string_of_b c)
	| IMem(_,a,b,i) -> (string_of_register a)^sep^(string_of_register b)^sep^(string_of_ic i)
	| ITest(_,a,o) -> (string_of_register a)^sep^(string_of_oc o)
	| Chk(a,c) -> (string_of_register a)^sep^(string_of_a c)
	| Bsr(o) -> (string_of_oc o)
	| Jsr(l) ->(string_of_lc l)
	| Ret(c) -> (string_of_register c)
	| Break -> ""
	| Syscall(a,b,sysc) -> (string_of_register a)^sep^(string_of_register b)^sep^(string_of_int (int_of_syscall sysc))
	| Data(f) -> (Int32.to_string (f ()))
    )

class label = fun name ->
object(self)
  val mutable anchor = (None:int option)
  method getName = name
  method getAnchor =
    match anchor with
	None -> failwith ("label "^(self#getName)^" still not anchored")
      | Some(n) -> n
  method setAnchor pc =
    match anchor with
	None -> anchor <- Some(pc)
      | Some(n) -> failwith ("label "^(self#getName)^" already anchored")
end

class code_generator =
object(self)
  val mutable len = 1
  val mutable code = Array.make 1 (None:instruction option)
  val mutable pc = 0
  val label_table = Hashtbl.create 10
  method emit instr =
    code.(pc) <- Some(instr);
    pc <- pc + 1;
    if (pc >= len) then
      begin
	let tmp = Array.make (2*len) None in
	  Array.blit code 0 tmp 0 len;
	  code <- tmp;
	  len <- 2*len
      end
  method dump =
    self#iter (fun _ instr -> print_string (string_of_instruction instr);print_newline())
  method iter f =
    for i = 0 to pc - 1 do
      let Some(instr) = code.(i) in
	f i instr
    done
  method fetch i =
    let Some(instr) = code.(i / 4) in instr
  method getSize = pc
  method getLabel name =
    if (name = "pc") || (name = "PC") then 
      freeze pc
    else
      let l =
	(try 
	   Hashtbl.find label_table name
	 with
	   Not_found -> 
	     let l = new label name in
	       Hashtbl.add label_table name l;
	       l)
      in (fun () -> l#getAnchor)
  method setLabel name =
    if (name = "pc") || (name = "PC") then ()
    else
      let l =
	(try 
	   Hashtbl.find label_table name
	 with
	   Not_found -> 
	     let l = new label name in
	       Hashtbl.add label_table name l;
	       l)
      in l#setAnchor pc
  method getLen = len
end
    
