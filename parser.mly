%{

%}

%token EOL ASSIGN RPAREN LPAREN NE EQ LT GT DIVIDE MULT PLUS MINUS STAGE COLON
%token SEMICOLON QUESTIONMARK CLAMP MIX COMMA
%token <int32> INT
%token <float> FLOAT
%token <Expr.var_param> VAR
%token <Expr.dest_var> DESTVAR
%token <Expr.lane_select array> CHANSELECT

%left QUESTIONMARK COLON
%left EQ LT GT
%left PLUS MINUS
%left MULT DIVIDE

%start <(int32 * Expr.expr) list> stage_defs

%%

stage_defs: option(EOL) 		{ [] }
	  | s = stage_def option(EOL) ss = stage_defs
					{ s :: ss }
;

stage_def: sn = stage_num se = stage_expr SEMICOLON
					{ (sn, se) }
;

stage_num: STAGE n = INT COLON		{ n }
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
	  | MINUS e = stage_expr	{ Expr.Neg e }
	  | a = DESTVAR ASSIGN b = stage_expr
					{ Expr.Assign (a, b) }
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
	  | e = stage_expr c = CHANSELECT
					{ Expr.Select (e, c) }
;

%%
