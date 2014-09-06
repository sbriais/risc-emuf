let filename = ref ""

let mem_size = ref 16000

let fast = ref true 

let gui = ref false

let dump = ref false

let open_file filename = 
  if filename = "--stdin" then stdin
  else Pervasives.open_in filename

let _ =
  let _ = Arg.parse 
	    ["-mem",Arg.Set_int(mem_size),"set memory size";
	     "-slow",Arg.Clear(fast),"use slow emulator (legacy)";
(* 	     "-gui",Arg.Set(gui),"use GUI"; *)
	     "-dump",Arg.Set(dump),"just dump code";
	     "--stdin",Arg.Unit(function () -> filename := "--stdin"),"use standard input";
	    ]
	    (fun s -> filename := s)
	    ("risc-emuf")
  in
  let in_channel = open_file !filename in
  let scanner = new Scanner.scanner (Scanner.charReader_of_in_channel in_channel) in
  let code = Parser.parse_program scanner in
    if !dump then
      code#dump
    else
      begin
	if !mem_size < code#getLen then
	  failwith "not enough memory (use -mem flag to increase memory)";
 	if !fast then 
	  let module Emulator = Fast_emul.Make(struct
						 let mem_size = !mem_size
						 let code = code
					       end)
	  in 
(* 	    if !gui then *)
(* 	      begin *)
(* 		let module Gui = Gui.Make(Emulator) in *)
(* 		  Gui.exec () *)
(* 	      end *)
(* 	    else *)
	      begin
		try
		  Emulator.exec ()
		with
		  | Emulator.Error(Emulator.Illegal) ->
		      prerr_string "illegal instruction";prerr_newline()
		  | Emulator.Error(Emulator.BrkExn) ->
		      prerr_string "break";prerr_newline()
		  | Emulator.Error(Emulator.ChkExn) ->
		      prerr_string "chk: out of bounds";prerr_newline()
		  | Emulator.Error(Emulator.Exit(n)) ->
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
	      end
	else
	  let emulator = new Emulator.emulator code (!mem_size) in
	    Pervasives.close_in in_channel;
	    try
	      emulator#start
	    with
	      | Emulator.Error(Emulator.Illegal(n)) ->
		  prerr_string "illegal instruction at ";prerr_int n;prerr_newline()
	      | Emulator.Error(Emulator.BusError(n)) ->
		  prerr_string "bus error: access at ";prerr_int n;prerr_newline()
	      | Emulator.Error(Emulator.InvalidReg) ->
		  prerr_string "invalid register";prerr_newline()
	      | Emulator.Error(Emulator.ChkError) ->
		  prerr_string "chk: out of bounds";prerr_newline()
	      | Emulator.Error(Emulator.BrkError) ->
		  prerr_string "break";prerr_newline()
	      | Emulator.Error(Emulator.Exit(n)) ->
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
      end
