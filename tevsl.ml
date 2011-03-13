let parseme s =
  let sbuf = Lexing.from_string s in
  let e = Parser.stage_def Lexer.token sbuf in
  e
