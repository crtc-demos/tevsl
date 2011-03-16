%{

%}

%token EOL ASSIGN RPAREN LPAREN NE EQ LT GT DIVIDE MULT PLUS MINUS STAGE COLON
%token SEMICOLON QUESTIONMARK CLAMP MIX COMMA
%token <int32> INT
%token <float> FLOAT
%token <Expr.var_param> VAR
%token <Expr.dest_var> DESTVAR
%token <Expr.lane_select array> CHANSELECT

%left PLUS MINUS
%left MULT DIVIDE

%start <int32 * Expr.expr> stage_def

%%

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
	  | a = select_expr EQ b = select_expr
					{ Expr.Ceq (a, b) }
	  | a = select_expr GT b = select_expr
					{ Expr.Cgt (a, b) }
	  | a = select_expr LT b = select_expr
					{ Expr.Clt (a, b) }
	  | a = stage_expr QUESTIONMARK b = stage_expr COLON c = stage_expr
					{ Expr.Ternary (a, b, c) }
	  | CLAMP LPAREN c = stage_expr RPAREN
					{ Expr.Clamp c }
	  | MIX LPAREN a = stage_expr COMMA b = stage_expr COMMA
	    c = stage_expr RPAREN
					{ Expr.Mix (a, b, c) }
;

select_expr: e = stage_expr		{ (e, [||]) }
	   | e = stage_expr c = CHANSELECT
					{ (e, c) }
;

%%
