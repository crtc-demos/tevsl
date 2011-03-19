{
  open Parser
}

let intnum = ['0'-'9']+
let floatnum = intnum "." intnum

(* Presume GX_CC_ONE, GX_CC_HALF, GX_CC_KONST, GX_CC_ZERO are written as
   numbers.  *)

let chanselect = "." ("r" | "g" | "b" | "a")+

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
	| "k0" chanselect
	| "k1" chanselect
	| "k2" chanselect
	| "k3" chanselect
	| "texc"
	| "texa"
	| "rasc"
	| "rasa"

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
	| "k0" -> Expr.K0 None
	| "k1" -> Expr.K1 None
	| "k2" -> Expr.K2 None
	| "k3" -> Expr.K3 None
	| "k0.r" -> Expr.K0 (Some Expr.R)
	| "k1.r" -> Expr.K1 (Some Expr.R)
	| "k2.r" -> Expr.K2 (Some Expr.R)
	| "k3.r" -> Expr.K3 (Some Expr.R)
	| "k0.g" -> Expr.K0 (Some Expr.G)
	| "k1.g" -> Expr.K1 (Some Expr.G)
	| "k2.g" -> Expr.K2 (Some Expr.G)
	| "k3.g" -> Expr.K3 (Some Expr.G)
	| "k0.b" -> Expr.K0 (Some Expr.B)
	| "k1.b" -> Expr.K1 (Some Expr.B)
	| "k2.b" -> Expr.K2 (Some Expr.B)
	| "k3.b" -> Expr.K3 (Some Expr.B)
	| "k0.a" -> Expr.K0 (Some Expr.A)
	| "k1.a" -> Expr.K1 (Some Expr.A)
	| "k2.a" -> Expr.K2 (Some Expr.A)
	| "k3.a" -> Expr.K3 (Some Expr.A)
	| "texc" -> Expr.Texc
	| "texa" -> Expr.Texa
	| "rasc" -> Expr.Rasc
	| "rasa" -> Expr.Rasa in
	VAR vt
      }
  | destvar as dv
      {
        let vt = match dv with
	  "tevprev" -> Expr.Tevprev
	| "tevreg0" -> Expr.Tevreg0
	| "tevreg1" -> Expr.Tevreg1
	| "tevreg2" -> Expr.Tevreg2 in
	DESTVAR vt
      }
  | "stage"	    { STAGE }
  | "+"		    { PLUS }
  | "-"		    { MINUS }
  | "*"		    { MULT }
  | "/"		    { DIVIDE }
  | ">"		    { GT }
  | "<"		    { LT }
  | "=="	    { EQ }
  | "!="	    { NE }
  | "("		    { LPAREN }
  | ")"		    { RPAREN }
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
  | "\n"	    { EOL }
  | (" "|"\t")+	    { token lexbuf }
