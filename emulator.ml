open Bigarray

exception BusError of int

class emulator = 
  let create_memory mem_size = 
    let mem = Array1.create int32 c_layout mem_size in
      for i = 0 to mem_size - 1 do
	mem.{i} <- Int32.zero
      done;
      mem
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
    if adr land 0x3 <> 0 then raise (BusError(adr))
    else
      try
	memory.{adr lsr 2}
      with Invalid_argument(_) -> raise (BusError(adr))
  method readByte adr =
    let b = self#readWord ((adr lsr 2) lsl 2) in
    let num = 3 - (adr land 0x3) in
      Int32.logand (Int32.shift_right_logical b (8*num)) (Int32.of_int 0xff)
  method writeWord adr w =
    if adr land 0x3 <> 0 then raise (BusError(adr))
    else
      try
	memory.{adr lsr 2} <- w
      with Invalid_argument(_) -> raise (BusError(adr))
  method writeByte adr b =
    let w = self#readWord ((adr lsr 2) lsl 2) in
    let num = 3 - (adr land 0x3) in
    let mask = Int32.lognot (Int32.shift_left (Int32.of_int 0xff) (8*num)) in
    let w = Int32.logand w mask in
    let w = Int32.logor w (Int32.shift_left (Int32.logand b (Int32.of_int 0xff)) (8*num)) in
      self#writeWord ((adr lsr 2) lsl 2) w
  method private fetch =
    Codec.decode_instruction (self#readWord pc)
  initializer
    self#init
end
