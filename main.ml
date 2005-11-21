let mem_size = ref 16000

let _ =
  let scanner = new Scanner.scanner (Scanner.charReader_of_in_channel stdin) in
  let code = Analyzer.analyze_program scanner in
  let emulator = new Emulator.emulator code (!mem_size) in
    code#dump
