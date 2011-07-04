%{

%}

%token EOL ASSIGN RPAREN LPAREN NE EQ LT GT LTE GTE DIVIDE MULT PLUS MINUS
%token STAGE COLON SEMICOLON QUESTIONMARK CLAMP MIX COMMA LSQUARE RSQUARE EOF
%token LBRACE RBRACE DOT ACCUM DEACCUM MATMUL MODULUS VEC3 ITEXCOORD
%token <int32> INT
%token <float> FLOAT
%token <int> TEXMAP TEXCOORD INDSCALE
%token <Expr.ind_matrix> INDMTX
%token <Expr.dyn_ind_matrix> D_INDMTX
%token <Expr.var_param> VAR
%token <Expr.dest_var> DESTVAR
%token <Expr.lane_select array> CHANSELECT

%left QUESTIONMARK COLON
%left EQ LT GT
%left PLUS MINUS ACCUM DEACCUM
%left MULT DIVIDE MODULUS
%right MATMUL

%start <(int * Expr.expr list) list> stage_defs

%%

stage_defs: EOF 			{ [] }
	  | s = stage_def ss = stage_defs
					{ s :: ss }
;

stage_def: sn = stage_num ses = stage_exprs
					{ (sn, ses) }
;

stage_num: STAGE n = INT COLON		{ Int32.to_int n }
	 | error			{ raise (Expr.Parsing_stage ($startpos,
								    $endpos)) }
;

stage_exprs: /* empty */		{ [] }
	   | se = stage_expr SEMICOLON ss = stage_exprs
					{ se :: ss }
;

stage_expr:
	     a = VAR DOT c = CHANSELECT ASSIGN b = rhs_expr
					 { Expr.Assign (Expr.destvar_of_var a,
					     c, b) }
	   | a = VAR ASSIGN b = rhs_expr
					 { Expr.Assign (Expr.destvar_of_var a,
					     [| Expr.R; Expr.G; Expr.B;
						Expr.A |], b) }
           | ITEXCOORD ASSIGN i = rhs_expr
					 { Expr.Assign (Expr.Itexc_dst,
					     [| Expr.LS_S; Expr.LS_T |], i) }
;

rhs_expr: n = INT			{ Expr.Int n }
	| n = FLOAT			{ Expr.Float n }
	| a = rhs_expr PLUS b = rhs_expr
				      { Expr.Plus (a, b) }
	| a = rhs_expr MINUS b = rhs_expr
				      { Expr.Minus (a, b) }
	| a = rhs_expr ACCUM b = rhs_expr
				      { Expr.Accum (a, b) }
	| a = rhs_expr DEACCUM b = rhs_expr
				      { Expr.Deaccum (a, b) }
	| a = rhs_expr MULT b = rhs_expr
				      { Expr.Mult (a, b) }
	| a = rhs_expr MATMUL b = rhs_expr
				      { Expr.Matmul (a, b) }
	| a = rhs_expr DIVIDE b = rhs_expr
				      { Expr.Divide (a, b) }
	| a = rhs_expr MODULUS b = rhs_expr
				      { Expr.Modulus (a, b) }
	| LPAREN e = rhs_expr RPAREN
	  			      { e }
	| v = VAR 			{ Expr.Var_ref v }
	| m = TEXMAP LSQUARE e = rhs_expr RSQUARE
				      { Expr.Texmap (m, e) }
        | t = TEXCOORD		{ Expr.Texcoord t }
	| s = INDSCALE		{ Expr.Indscale s }
	| m = INDMTX			{ Expr.Indmtx m }
	| MINUS e = rhs_expr	{ Expr.Neg e }
	| ITEXCOORD			{ Expr.Itexcoord }
	| a = rhs_expr EQ b = rhs_expr
				      { Expr.Ceq (a, b) }
	| a = rhs_expr GT b = rhs_expr
				      { Expr.Cgt (a, b) }
	| a = rhs_expr LT b = rhs_expr
				      { Expr.Clt (a, b) }
	| a = rhs_expr QUESTIONMARK b = rhs_expr COLON c = rhs_expr
				      { Expr.Ternary (a, b, c) }
	| CLAMP LPAREN c = rhs_expr RPAREN
				      { Expr.Clamp c }
	| MIX LPAREN a = rhs_expr COMMA b = rhs_expr COMMA
	  c = rhs_expr RPAREN
				      { Expr.Mix (a, b, c) }
	| VEC3 LPAREN a = rhs_expr COMMA b = rhs_expr COMMA
	  c = rhs_expr RPAREN
				      { Expr.Vec3 (a, b, c) }
	| c = D_INDMTX LPAREN e = rhs_expr RPAREN
				      { Expr.D_indmtx (c, e) }
	| e = rhs_expr DOT c = CHANSELECT
				      { Expr.Select (e, c) }
	| e = rhs_expr LBRACE c = CHANSELECT RBRACE
				      { Expr.Concat (e,
					  Array.of_list (List.rev
					    (Array.to_list c))) }
;

%%
