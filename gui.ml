(*
  DLX emulator
  Copyright (C) 2005-2014 Sebastien Briais (sbriais@free.fr)

  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

module Make(Emulator:Fast_emul.Emulator) =
  struct

    let hexstring_of_int32 n = Format.sprintf "%08lX" n

    let add_refresh,refresh =
      let refresh_action = ref [] in
      let add_refresh f =
	refresh_action := f::!refresh_action
      in
      let refresh () =
	List.iter (function f -> f ()) !refresh_action;
	Tk.update ()
      in add_refresh,refresh

    let safe_callback c =
      try c ()
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
	| Failure(s) ->
	    prerr_string "Uncaught exception: ";
	    prerr_string s;
	    prerr_newline ()
	| Invalid_argument(s) ->
	    prerr_string "Uncaught exception: ";
	    prerr_string "invalid argument ";
	    prerr_string s;
	    prerr_newline ()
	| _ ->
	    prerr_string "Uncaught exception: ";
	    prerr_newline ()

    let run_callback () =
      safe_callback (function () ->
		       while true do
			 Emulator.tick ();
		       done);
      refresh()

    let step_callback () =
      safe_callback Emulator.tick;
      refresh ()

    let reset_callback () =
      safe_callback Emulator.reset;
      refresh()

    let string_of_value addr value =
      let st = Codec.decode_instruction value in
      let s1 = hexstring_of_int32 addr in
      let s2 = hexstring_of_int32 value in
      let s3 = if addr = Emulator.getPC() then "> " else "  " in
      let s4 = Risc.string_of_instruction st in
	s1^": "^s2^" "^s3^" "^s4

    let dump_mem b l =
      if b then
	begin
	  Listbox.delete ~first:(`Num(0)) ~last:`End l;
	  for i = 0 to Emulator.mem_size-1 do
	    let v = Emulator.read_word (Int32.of_int (4*i)) in
	      Listbox.insert ~index:`End ~texts:[string_of_value (Int32.shift_left (Int32.of_int i) 2) v] l
	  done
	end
      else
	begin
	  let `Num(i) = Listbox.nearest l ~y:0 in
	  let imin = max 0 (i-50) and imax = min (i+50) (Listbox.size l) in
	    Listbox.delete ~first:(`Num(imin)) ~last:(`Num(imax)) l;
	    for i = imin to imax do
	      let v = Emulator.read_word (Int32.of_int (4*i)) in
		Listbox.insert ~index:(`Num(i)) ~texts:[string_of_value (Int32.shift_left (Int32.of_int i) 2) v] l
	    done
	end

    let mkGui top =
      Wm.title_set top "Risc Emulator";
      let base = Frame.create top in
      let registers = Frame.create base in
      let base2 = Frame.create base in
      let base3 = Frame.create base in
      let code = Frame.create base2 in
      let mem = Frame.create base2 in
	Tk.pack ~side:`Top ~expand:true ~fill:`Both [base];
	Tk.pack ~side:`Top ~expand:true [registers;base2];
	Tk.pack ~side:`Left ~expand:true [code;mem];
	Tk.pack ~side:`Top ~expand:true [base3];
	(* bottom bar *)
	let bpc = Button.create ~text:"PC" base3 in
	let lpc = Label.create ~text:(hexstring_of_int32 (Emulator.getPC())) base3 in
	  add_refresh (function () ->
			 Label.configure lpc ~text:(hexstring_of_int32 (Emulator.getPC())));
	  let breset = Button.create ~text:"Reset" ~command:reset_callback base3 in
	  let brun = Button.create ~text:"Run" ~command:run_callback base3 in
	  let bstep = Button.create ~text:"Step" ~command:step_callback base3 in
	    Tk.pack ~side:`Left ~expand:true [bpc];
	    Tk.pack ~side:`Left ~expand:true [lpc];
	    Tk.pack ~side:`Left ~expand:true [breset;brun;bstep];
	    (* middle bar *)
	    let lcode = Listbox.create ~selectmode:`Browse ~width:40 code in
	      dump_mem true lcode;
	      Tk.pack ~side:`Left ~expand:true [lcode];
	      add_refresh (function () -> Listbox.see ~index:(`Num(Int32.to_int (Emulator.getPC()) / 4)) lcode;dump_mem false lcode;Listbox.see ~index:(`Num(Int32.to_int (Emulator.getPC()) / 4)) lcode);
	      let lmem = Listbox.create ~width:40 mem in
		dump_mem true lmem;
		Tk.pack ~side:`Left ~expand:true [lmem];
		add_refresh (function () -> dump_mem false lmem);
	    (* registers *)
	    let rwidgets = Array.map
			     (List.map (fun r ->
					  let w = Frame.create registers in
					  let b = Button.create ~text:("R"^(Int32.to_string r)) w in
					  let l = Label.create ~text:(hexstring_of_int32 (Emulator.register_get r)) w in
					    Tk.pack ~side:`Left ~expand:true [b];
					    Tk.pack ~side:`Left ~expand:true [l];
					    add_refresh (function () ->
							   Label.configure l ~text:(hexstring_of_int32 (Emulator.register_get r)));
					    w))
			     [|[0l;4l;8l;12l;16l;20l;24l;28l];
			       [1l;5l;9l;13l;17l;21l;25l;29l];
			       [2l;6l;10l;14l;18l;22l;26l;30l];
			       [3l;7l;11l;15l;19l;23l;27l;31l]|]
	in
	  for i = 0 to 4-1 do
	    Grid.configure ~row:i (rwidgets.(i))
	  done

    let exec () =
      let top = Tk.openTk () in
	Tk.appname_set "Risc Emulator";
	mkGui top;
	Tk.mainLoop ()

  end
