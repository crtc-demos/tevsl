{
  open Parser
}

let intnum = ['0'-'9']+
let floatnum = intnum "." intnum

(* Presume GX_CC_ONE, GX_CC_HALF, GX_CC_KONST, GX_CC_ZERO are written as
   numbers.  *)

let chanselect = ("r" | "g" | "b" | "a")+

(* We're British thankyou, allow proper spelling.  *)

let colour = "colour" | "color"

let var = "tev"
	| "cr0"
	| "cr1"
	| "cr2"
	| "ras"
	| "tex"
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
	  "tev" -> Expr.Tev
	| "cr0" -> Expr.CR 0
	| "cr1" -> Expr.CR 1
	| "cr2" -> Expr.CR 2
	| "ras" -> Expr.Raster
	| "tex" -> Expr.Texture
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
	| _ -> failwith "Bad variable" in
	VAR vt
      }
  | "texmap" (intnum as n)
		    { TEXMAP (int_of_string n) }
  | "texcoord" (intnum as n)
		    { TEXCOORD (int_of_string n) }
  | "indmtx" (intnum as n)
  		    { INDMTX (Expr.Ind_matrix (int_of_string n)) }
  | "s_dynmtx"	    { D_INDMTX Expr.Dyn_S }
  | "t_dynmtx"	    { D_INDMTX Expr.Dyn_T }
  | "indscale" (intnum as n)
		    { INDSCALE (int_of_string n) }
  | "stage"	    { STAGE }
  | "itexcoord"     { ITEXCOORD }
  | "+"		    { PLUS }
  | "-"		    { MINUS }
  | "@+"	    { ACCUM }
  | "@-"	    { DEACCUM }
  | "**"	    { MATMUL }
  | "*"		    { MULT }
  | "/"		    { DIVIDE }
  | "%"		    { MODULUS }
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
  | "{"		    { LBRACE }
  | "}"		    { RBRACE }
  | "="		    { ASSIGN }
  | ":"		    { COLON }
  | ";"		    { SEMICOLON }
  | ","		    { COMMA }
  | "?"		    { QUESTIONMARK }
  | "clamp"	    { CLAMP }
  | "mix"	    { MIX }
  | "vec3"	    { VEC3 }
  | "."		    { DOT }
  | chanselect as c { let arr = Array.create (String.length c) Expr.R in
		      for i = 0 to String.length c - 1 do
		        arr.(i) <- match c.[i] with
			  'r' -> Expr.R
			| 'g' -> Expr.G
			| 'b' -> Expr.B
			| 'a' -> Expr.A
			| _ -> failwith "Bad channel selector"
		      done;
		      CHANSELECT arr }
  | (" "|"\t"|"\n")+
  		    { token lexbuf }
  | "#" [^'\n']* "\n"
  		    { token lexbuf }
  | eof             { EOF }
