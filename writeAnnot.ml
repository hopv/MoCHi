open Location
open Stypes
open Parsetree


let print_position pp pos =
  if pos = Lexing.dummy_pos then
    Format.fprintf pp "--"
  else
    Format.fprintf pp "%S %d %d %d"
      pos.Lexing.pos_fname pos.Lexing.pos_lnum
      pos.Lexing.pos_bol
      pos.Lexing.pos_cnum

let make loc typ =
  if loc <> Location.none then [loc, typ] else []

let rec process_pat env {pc_lhs; pc_guard; pc_rhs} =
  process_pattern env pc_lhs @
  process_expopt env pc_guard @
  process_expression env pc_rhs
and process_binding env {pvb_pat; pvb_expr} =
  process_pattern env pvb_pat @
  process_expression env pvb_expr
and process_pattern env p =
  match p.ppat_desc with
  | Ppat_any -> []
  | Ppat_var s ->
      (try
         make p.ppat_loc (List.assoc s.txt env)
       with Not_found ->
         [])
  | Ppat_alias _ -> []
  | Ppat_constant _ -> []
  | Ppat_tuple _ -> []
  | Ppat_construct _ -> []
  | Ppat_variant _ -> []
  | Ppat_record _ -> []
  | Ppat_array _ -> []
  | Ppat_or _ -> []
  | Ppat_constraint _ -> []
  | Ppat_type _ -> []
  | Ppat_lazy _ -> []
  | Ppat_unpack _ -> []
  | Ppat_interval _ -> []
  | Ppat_exception _ -> []
  | Ppat_extension _ -> []
  | _ -> [] (* for after 4.05 *)
and process_expopt env eopt = Util.Option.map_default (process_expression env) [] eopt
and process_expression env e =
  match e.pexp_desc with
  | Pexp_ident(x) ->
      (try
          make e.pexp_loc (List.assoc (Longident.last x.txt) env)
       with Not_found ->
         [])
  | Pexp_constant _ ->
      []
  | Pexp_let(_, binds, e) ->
      Util.List.concat_map (process_binding env) binds @
        process_expression env e
  | Pexp_function pats ->
      Util.List.concat_map (process_pat env) pats
  | Pexp_fun(_, eopt, p, e) ->
      process_expopt env eopt @
      process_pattern env p @
      process_expression env e
  | Pexp_apply(e, les) ->
      process_expression env e @
        Util.List.concat_map (fun (_, e) -> process_expression env e) les
  | Pexp_match(e ,pats) ->
      process_expression env e @
        Util.List.concat_map (process_pat env) pats
  | Pexp_try(e, pats) ->
      process_expression env e @
        Util.List.concat_map (process_pat env) pats
  | Pexp_tuple es ->
      Util.List.concat_map (process_expression env) es
  | Pexp_construct(_, eopt) ->
      process_expopt env eopt
  | Pexp_variant(_, eopt) ->
      process_expopt env eopt
  | Pexp_record(fields, eopt) ->
      Util.List.concat_map (fun (_, e) -> process_expression env e) fields @
        process_expopt env eopt
  | Pexp_field(e, _) ->
      process_expression env e
  | Pexp_setfield(e1, _, e2) ->
      process_expression env e1 @
        process_expression env e2
  | Pexp_array(es) ->
      Util.List.concat_map (process_expression env) es
  | Pexp_ifthenelse(e1, e2, eopt) ->
      process_expression env e1 @
        process_expression env e2 @
        process_expopt env eopt
  | Pexp_sequence(e1, e2) ->
      process_expression env e1 @
        process_expression env e2
  | Pexp_while(e1, e2) ->
      process_expression env e1 @
        process_expression env e2
  | Pexp_for(_, e1, e2, _, e3) ->
      process_expression env e1 @
        process_expression env e2 @
        process_expression env e3
  | Pexp_constraint(e, _) ->
      process_expression env e
  | Pexp_send(e, _) ->
      process_expression env e
  | Pexp_new(_) ->
      []
  | Pexp_setinstvar(_, e) ->
      process_expression env e
  | Pexp_override(ies) ->
      Util.List.concat_map (fun (_, e) -> process_expression env e) ies
  | Pexp_letmodule(_, _, e) ->
      []
  | Pexp_assert(e) ->
      process_expression env e
  | Pexp_lazy(e) ->
      process_expression env e
  | Pexp_poly(e, _) ->
      process_expression env e
  | Pexp_object(_) ->
      Util.unsupported "Not implemented: writeAnnot"
  | Pexp_newtype(_, e) ->
      process_expression env e
  | Pexp_pack(_) ->
      Util.unsupported "Not implemented: writeAnnot"
  | Pexp_open _ -> Util.unsupported "Not implemented: writeAnnot"
  | Pexp_coerce (_, _, _) -> Util.unsupported "Not implemented: writeAnnot"
  | Pexp_extension _ -> Util.unsupported "Not implemented: writeAnnot"
  | Pexp_unreachable -> Util.unsupported "Not implemented: writeAnnot"
  | _ -> Util.unsupported "Not implemented: writeAnnot" (* for after 4.05 *)

let process_top_level_phrase env = function
  | Ptop_dir _ ->
      []
  | Ptop_def struc ->
      let aux si =
        match si.pstr_desc with
        | Pstr_eval(e, _) ->
           process_expression env e
        | Pstr_value(_, binds) ->
            Util.List.concat_map (process_binding env) binds
        | Pstr_primitive _ -> []
        | Pstr_type _ -> []
        | Pstr_exception _ -> []
        | Pstr_module _ -> []
        | Pstr_recmodule _ -> []
        | Pstr_modtype _ -> []
        | Pstr_open _ -> []
        | Pstr_class _ -> []
        | Pstr_class_type _ -> []
        | Pstr_include _ -> []
        | Pstr_typext _ -> []
        | Pstr_attribute _ -> []
        | Pstr_extension _ -> []
      in
      Util.List.concat_map aux struc


let f filename orig env =
  let filename = Util.Filename.change_extension filename "annot" in
  let oc = Format.formatter_of_out_channel (open_out filename) in
    List.iter
      (fun (loc, typ) ->
         if loc.loc_start <> Lexing.dummy_pos && loc.loc_end <> Lexing.dummy_pos then
           let _ = print_position oc loc.loc_start in
           let _ = Format.fprintf oc " " in
           let _ = print_position oc loc.loc_end in
           let _ = Format.fprintf oc "@.type(@.  " in
           let _ = Format.fprintf oc "%a" Ref_type.print typ in
             Format.fprintf oc "@.)@.")
      (Util.List.concat_map (process_top_level_phrase env) orig)
