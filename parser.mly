%{

%}

%token EOL ASSIGN RPAREN LPAREN NE EQ LT GT LTE GTE DIVIDE MULT PLUS MINUS
%token STAGE COLON SEMICOLON QUESTIONMARK CLAMP MIX COMMA LSQUARE RSQUARE EOF
%token LBRACE RBRACE DOT
%token <int32> INT
%token <float> FLOAT
%token <int> TEXMAP TEXCOORD
%token <Expr.var_param> VAR
%token <Expr.dest_var> DESTVAR
%token <Expr.lane_select array> CHANSELECT

%left QUESTIONMARK COLON
%left EQ LT GT
%left PLUS MINUS
%left MULT DIVIDE

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
;

stage_exprs: /* empty */		{ [] }
	   | se = stage_expr SEMICOLON ss = stage_exprs
					{ se :: ss }
;

stage_expr: n = INT			{ Expr.Int n }
	  | n = FLOAT			{ Expr.Float n }
	  | a = stage_expr PLUS b = stage_expr
					{ Expr.Plus (a, b) }
	  | a = stage_expr MINUS b = stage_expr
					{ Expr.Minus (a, b) }
	  | a = stage_expr MULT b = stage_expr
					{ Expr.Mult (a, b) }
	  | a = stage_expr DIVIDE b = stage_expr
					{ Expr.Divide (a, b) }
	  | LPAREN e = stage_expr RPAREN
	  				{ e }
	  | v = VAR 			{ Expr.Var_ref v }
	  | m = TEXMAP LSQUARE c = TEXCOORD RSQUARE
					{ Expr.Texmap (m, c) }
	  | MINUS e = stage_expr	{ Expr.Neg e }
	  | a = DESTVAR DOT c = CHANSELECT ASSIGN b = stage_expr
					{ Expr.Assign (a, c, b) }
	  | a = DESTVAR ASSIGN b = stage_expr
					{ Expr.Assign (a,
					    [| Expr.R; Expr.G; Expr.B;
					       Expr.A |], b) }
	  | a = stage_expr EQ b = stage_expr
					{ Expr.Ceq (a, b) }
	  | a = stage_expr GT b = stage_expr
					{ Expr.Cgt (a, b) }
	  | a = stage_expr LT b = stage_expr
					{ Expr.Clt (a, b) }
	  | a = stage_expr QUESTIONMARK b = stage_expr COLON c = stage_expr
					{ Expr.Ternary (a, b, c) }
	  | CLAMP LPAREN c = stage_expr RPAREN
					{ Expr.Clamp c }
	  | MIX LPAREN a = stage_expr COMMA b = stage_expr COMMA
	    c = stage_expr RPAREN
					{ Expr.Mix (a, b, c) }
	  | e = stage_expr DOT c = CHANSELECT
					{ Expr.Select (e, c) }
	  | e = stage_expr LBRACE c = CHANSELECT RBRACE
					{ Expr.Concat (e,
					    Array.of_list (List.rev
					      (Array.to_list c))) }
;

%%
