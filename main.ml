open Emulator

let filename = ref ""

let mem_size = ref 16000

let _ =
  let _ = Arg.parse 
	    ["-mem",Arg.Set_int(mem_size),"set memory size"]
	    (fun s -> filename := s)
	    ("risc-emuf")
  in
  let in_channel = Pervasives.open_in (!filename) in
  let scanner = new Scanner.scanner (Scanner.charReader_of_in_channel in_channel) in
  let code = Analyzer.analyze_program scanner in
  let emulator = new Emulator.emulator code (!mem_size) in
    Pervasives.close_in in_channel;
    try
      emulator#start
    with 
      | Error(Illegal(n)) -> 
	  prerr_string "illegal instruction at ";prerr_int n;prerr_newline()
      | Error(BusError(n)) -> 
	  prerr_string "bus error: access at ";prerr_int n;prerr_newline()
      | Error(InvalidReg) ->
	  prerr_string "invalid register";prerr_newline()
      | Error(ChkError) ->
	  prerr_string "chk: out of bounds";prerr_newline()
      | Error(BrkError) ->
	  prerr_string "break";prerr_newline()
      | Error(Exit(n)) ->
	  if (Int32.compare n Int32.zero) = 0 then
	    begin
	      prerr_string "program exited successfully";prerr_newline()
	    end
	  else
	    begin
	      prerr_string "program exited with error status code ";
	      prerr_string (Int32.to_string n);
	      prerr_newline()
	    end
