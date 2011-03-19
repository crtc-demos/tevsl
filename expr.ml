type expr =
    Int of int32
  | Float of float
  | Plus of expr * expr
  | Minus of expr * expr
  | Mult of expr * expr
  | Divide of expr * expr
  | Var_ref of var_param
  | Neg of expr
  | Clamp of expr
  | Mix of expr * expr * expr
  | Assign of dest_var * expr
  | Ceq of select_expr * select_expr
  | Cgt of select_expr * select_expr
  | Clt of select_expr * select_expr
  | Ternary of expr * expr * expr

and select_expr =
  expr * lane_select array

and lane_select = R | G | B | A

and var_param =
    Cprev
  | Aprev
  | C0
  | A0
  | C1
  | A1
  | C2
  | A2
  | K0 of lane_select option
  | K1 of lane_select option
  | K2 of lane_select option
  | K3 of lane_select option
  | Texc
  | Texa
  | Rasc
  | Rasa
  | Extracted_const

and dest_var =
    Tevprev
  | Tevreg0
  | Tevreg1
  | Tevreg2

and const_setting =
    KCSEL_1
  | KCSEL_7_8
  | KCSEL_3_4
  | KCSEL_5_8
  | KCSEL_1_2
  | KCSEL_3_8
  | KCSEL_1_4
  | KCSEL_1_8
  | KCSEL_K0
  | KCSEL_K1
  | KCSEL_K2
  | KCSEL_K3
  | KCSEL_K0_R
  | KCSEL_K1_R
  | KCSEL_K2_R
  | KCSEL_K3_R
  | KCSEL_K0_G
  | KCSEL_K1_G
  | KCSEL_K2_G
  | KCSEL_K3_G
  | KCSEL_K0_B
  | KCSEL_K1_B
  | KCSEL_K2_B
  | KCSEL_K3_B
  | KCSEL_K0_A
  | KCSEL_K1_A
  | KCSEL_K2_A
  | KCSEL_K3_A

(* 
    TevColorIn: a b c d
    TevColorOp: tevop tevbias tevscale clamp tevregid

    regular operation:

    tevregid = (d [+/-] ((1-c)*a + c*b) + tevbias) * tevscale
*)

type arith_op =
  {
    a : var_setting;
    b : var_setting;
    c : var_setting;
    d : var_setting;
    op : tev_op;
    bias : bias_values;
    scale : scale_values;
    clamp : bool;
    result : dest_var
  }

(*
    tevregid = d + ((a OP b) ? c : 0)
*)

and compare_op =
  {
    cmp_a : var_setting;
    cmp_b : var_setting;
    cmp_c : var_setting;
    cmp_d : var_setting;
    cmp_op : tev_cmp_op;
    cmp_result : dest_var
  }

and var_setting =
    CC_cprev
  | CC_aprev
  | CC_c0
  | CC_a0
  | CC_c1
  | CC_a1
  | CC_c2
  | CC_a2
  | CC_texc
  | CC_texa
  | CC_rasc
  | CC_rasa
  | CC_one
  | CC_half
  | CC_const
  | CC_zero

and tev_op =
    OP_add
  | OP_sub

and tev_cmp_op =
    CMP_r8_gt
  | CMP_r8_eq
  | CMP_gr16_gt
  | CMP_gr16_eq
  | CMP_bgr24_gt
  | CMP_bgr24_eq
  | CMP_rgb8_gt
  | CMP_rgb8_eq

and bias_values =
    TB_zero
  | TB_addhalf
  | TB_subhalf

and scale_values =
    CS_scale_1
  | CS_scale_2
  | CS_scale_4
  | CS_divide_2

and tev =
    Arith of arith_op
  | Comp of compare_op

