{
  open Parser
}

let intnum = ['0'-'9']+
let floatnum = intnum "." intnum

(* Presume GX_CC_ONE, GX_CC_HALF, GX_CC_KONST, GX_CC_ZERO are written as
   numbers.  *)

let chanselect = "." ("r" | "g" | "b" | "a")+

(* We're British thankyou, allow proper spelling.  *)

let colour = "colour" | "color"

let var = "cprev"
        | "aprev"
	| "c0"
	| "a0"
	| "c1"
	| "a1"
	| "c2"
	| "a2"
	| "k0"
	| "k1"
	| "k2"
	| "k3"
	| colour "0"
	| "alpha0"
	| colour "0a0"
	| colour "1"
	| "alpha1"
	| colour "1a1"
	| colour "zero"
	| "alphabump"
	| "alphabumpn"
     (* | "texc"
	| "texa"
	| "rasc"
	| "rasa" *)

let destvar = "tevprev"
            | "tevreg0"
	    | "tevreg1"
	    | "tevreg2"

rule token = parse
    intnum as n     { INT (Int32.of_string n) }
  | floatnum as n   { FLOAT (float_of_string n) }
  | var as v
      {
        let vt = match v with
	  "cprev" -> Expr.Cprev
	| "aprev" -> Expr.Aprev
	| "c0" -> Expr.C0
	| "a0" -> Expr.A0
	| "c1" -> Expr.C1
	| "a1" -> Expr.A1
	| "c2" -> Expr.C2
	| "a2" -> Expr.A2
	| "k0" -> Expr.K0
	| "k1" -> Expr.K1
	| "k2" -> Expr.K2
	| "k3" -> Expr.K3
	| "colour0" | "color0" -> Expr.Colour0
	| "alpha0" -> Expr.Alpha0
	| "colour0a0" | "color0a0" -> Expr.Colour0A0
	| "colour1" | "color1" -> Expr.Colour1
	| "alpha1" -> Expr.Alpha1
	| "colour1a1" | "color1a1" -> Expr.Colour1A1
	| "colourzero" | "colorzero" -> Expr.ColourZero
	| "alphabump" -> Expr.AlphaBump
	| "alphabumpn" -> Expr.AlphaBumpN
     (* | "texc" -> Expr.Texc
	| "texa" -> Expr.Texa
	| "rasc" -> Expr.Rasc
	| "rasa" -> Expr.Rasa *)
	| _ -> failwith "Bad variable" in
	VAR vt
      }
  | destvar as dv
      {
        let vt = match dv with
	  "tevprev" -> Expr.Tevprev
	| "tevreg0" -> Expr.Tevreg0
	| "tevreg1" -> Expr.Tevreg1
	| "tevreg2" -> Expr.Tevreg2
	| _ -> failwith "Bad dest variable" in
	DESTVAR vt
      }
  | "texmap" (intnum as n)
		    { TEXMAP (int_of_string n) }
  | "texcoord" (intnum as n)
		    { TEXCOORD (int_of_string n) }
  | "stage"	    { STAGE }
  | "+"		    { PLUS }
  | "-"		    { MINUS }
  | "*"		    { MULT }
  | "/"		    { DIVIDE }
  | ">"		    { GT }
  | "<"		    { LT }
  | ">="	    { GTE }
  | "<="	    { LTE }
  | "=="	    { EQ }
  | "!="	    { NE }
  | "("		    { LPAREN }
  | ")"		    { RPAREN }
  | "["		    { LSQUARE }
  | "]"		    { RSQUARE }
  | "="		    { ASSIGN }
  | ":"		    { COLON }
  | ";"		    { SEMICOLON }
  | ","		    { COMMA }
  | "?"		    { QUESTIONMARK }
  | "clamp"	    { CLAMP }
  | "mix"	    { MIX }
  | chanselect as c { let arr = Array.create (String.length c - 1) Expr.R in
		      for i = 1 to String.length c - 1 do
		        arr.(i - 1) <- match c.[i] with
			  'r' -> Expr.R
			| 'g' -> Expr.G
			| 'b' -> Expr.B
			| 'a' -> Expr.A
			| _ -> failwith "Bad channel selector"
		      done;
		      CHANSELECT arr }
  | (" "|"\t"|"\n")+
  		    { token lexbuf }
  | eof             { EOF }
