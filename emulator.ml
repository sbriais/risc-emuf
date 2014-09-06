open Bigarray
open Risc

type error = BusError of int | SaveReg of int | Illegal

exception Error of error

class emulator = 
  let create_memory mem_size = 
    let mem = Array1.create int32 c_layout mem_size in
      for i = 0 to mem_size - 1 do
	mem.{i} <- Int32.zero
      done;
      mem
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
  in
    fun code mem_size ->
object(self)
  val memory = create_memory mem_size 
  val mutable pc = 0
  val registers = Array.make 32 (Int32.zero)
  method private init =
    code#iter 
      (fun i instr ->
	 memory.{i} <- Codec.code_instruction instr)
  method readWord adr =
    if adr land 0x3 <> 0 then raise (Error(BusError(adr)))
    else
      try
	memory.{adr lsr 2}
      with Invalid_argument(_) -> raise (Error(BusError(adr)))
  method readByte adr =
    let b = self#readWord ((adr lsr 2) lsl 2) in
    let num = 3 - (adr land 0x3) in
      Int32.logand (Int32.shift_right_logical b (8*num)) (Int32.of_int 0xff)
  method writeWord adr w =
    if adr land 0x3 <> 0 then raise (Error(BusError(adr)))
    else
      try
	memory.{adr lsr 2} <- w
      with Invalid_argument(_) -> raise (Error(BusError(adr)))
  method writeByte adr b =
    let w = self#readWord ((adr lsr 2) lsl 2) in
    let num = 3 - (adr land 0x3) in
    let mask = Int32.lognot (Int32.shift_left (Int32.of_int 0xff) (8*num)) in
    let w = Int32.logand w mask in
    let w = Int32.logor w (Int32.shift_left (Int32.logand b (Int32.of_int 0xff)) (8*num)) in
      self#writeWord ((adr lsr 2) lsl 2) w
  method private fetch =
    Codec.decode_instruction (self#readWord pc)
  method private exec instr =
    let val_of_ariiu = function
      | AR(R(n)) -> registers.(n)
      | AI(Signed(f)) -> Int32.of_int (f ())
      | AIU(Unsigned(f)) -> Int32.of_int (f ())
    and val_of_bri = function
      | BR(R(n)) -> registers.(n)
      | BI(Signed(f)) -> Int32.of_int (f ())
    in
    let save_reg n v =
      if (n <= 0) || (n > 31) then raise (Error(SaveReg(n)))
      else registers.(n) <- v
    in
      match instr with
	| IArith(op,R(a),R(b),c) -> save_reg a ((int_op_of_arith_op op) (registers.(b)) (val_of_ariiu c))
	| ILog(op,R(a),R(b),c) -> save_reg a ((int_op_of_log_op op) (registers.(b)) (val_of_ariiu c))
	| ISh(op,R(a),R(b),c) -> save_reg a ((int_op_of_sh_op op) (registers.(b)) (val_of_bri c))
	| _ -> raise (Error(Illegal))
  initializer
    self#init
end
