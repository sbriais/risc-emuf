open Bigarray

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
  initializer
    self#init
end
