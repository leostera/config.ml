open Ppxlib

let tag = "cfg"
let short_tag = "config"
let is_config_tag str = String.equal str tag || String.equal str short_tag

let user_env =
  Unix.environment () |> Array.to_list
  |> List.map (fun kv ->
         let[@warning "-8"] (k :: v) = String.split_on_char '=' kv in
         (k, String.concat "=" v))

let env =
  user_env
  @ [
      ("target_os", Cfg.target_os);
      ("target_arch", Cfg.target_arch);
      ("target_env", Cfg.target_env);
    ]
  |> List.sort_uniq (fun (k1, _) (k2, _) -> String.compare k1 k2)

let () =
  if Option.is_some (Sys.getenv_opt "CONFIG_DEBUG") then (
    Format.printf "Config PPX running with environment:\n\n%!";
    List.iter (fun (k, v) -> Format.printf "  %s = %S\r\n" k v) env;
    Format.printf "\n%!")

let env = List.map (fun (k, v) -> (k, Cfg_lang.Parser.String v)) env

let eval_attr attr =
  if not (is_config_tag attr.attr_name.txt) then `keep
  else
    let loc = attr.attr_loc in
    (* Printf.printf "\n\nattr name: %S\n\n" attr.attr_name.txt; *)
    match attr.attr_payload with
    | PStr [ { pstr_desc = Pstr_eval (e, []); _ } ] ->
        (* let e_ = Pprintast.string_of_expression e in *)
        (* Printf.printf "\n\npayload: %S\n\n" e_; *)
        if Cfg_lang.eval ~loc ~env e then `keep else `drop
    | _ -> `keep

let rec should_keep attrs =
  match attrs with
  | [] -> `keep
  | attr :: attrs -> if eval_attr attr = `drop then `drop else should_keep attrs

let rec should_keep_many list fn =
  match list with
  | [] -> `keep
  | item :: list ->
      if should_keep (fn item) = `drop then `drop else should_keep_many list fn

let apply_config_on_types (tds : type_declaration list) =
  List.filter_map
    (fun td ->
      match td with
      | {
       ptype_kind = Ptype_abstract;
       ptype_manifest =
         Some
           ({ ptyp_desc = Ptyp_variant (rows, closed_flag, labels); _ } as
            manifest);
       _;
      } ->
          let rows =
            List.filter_map
              (fun row ->
                if should_keep row.prf_attributes = `keep then Some row
                else None)
              rows
          in

          if rows = [] then None
          else
            Some
              {
                td with
                ptype_manifest =
                  Some
                    {
                      manifest with
                      ptyp_desc = Ptyp_variant (rows, closed_flag, labels);
                    };
              }
      | { ptype_kind = Ptype_variant cstrs; _ } ->
          let cstrs =
            List.filter_map
              (fun cstr ->
                if should_keep cstr.pcd_attributes = `keep then Some cstr
                else None)
              cstrs
          in

          if cstrs = [] then None
          else Some { td with ptype_kind = Ptype_variant cstrs }
      | { ptype_kind = Ptype_record labels; _ } ->
          let labels =
            List.filter_map
              (fun label ->
                if should_keep label.pld_attributes = `keep then Some label
                else None)
              labels
          in

          if labels = [] then None
          else Some { td with ptype_kind = Ptype_record labels }
      | _ -> Some td)
    tds

let apply_config_on_cases (cases : cases) =
  List.filter
    (fun case -> should_keep case.pc_rhs.pexp_attributes = `keep)
    cases

let rec apply_config_on_expression (exp : expression) =
  let pexp_desc =
    match exp.pexp_desc with
    | Pexp_try (exp, cases) ->
        let exp = apply_config_on_expression exp in
        let cases = apply_config_on_cases cases in
        Pexp_try (exp, cases)
    | Pexp_match (exp, cases) ->
        let exp = apply_config_on_expression exp in
        let cases = apply_config_on_cases cases in
        Pexp_match (exp, cases)
    | Pexp_function (params, constraint_, Pfunction_body exp) ->
        let exp = apply_config_on_expression exp in
        Pexp_function (params, constraint_, Pfunction_body exp)
    | Pexp_function (params, constraint_, Pfunction_cases (cases, locs, attrs))
      ->
        let cases = apply_config_on_cases cases in
        Pexp_function (params, constraint_, Pfunction_cases (cases, locs, attrs))
    | Pexp_let (rec_flag, vbs, exp) ->
        let exp = apply_config_on_expression exp in
        Pexp_let (rec_flag, vbs, exp)
    | _ -> exp.pexp_desc
  in
  { exp with pexp_desc }

let apply_config_on_value_bindings (vbs : value_binding list) =
  List.filter_map
    (fun vb ->
      if should_keep vb.pvb_attributes = `keep then
        Some { vb with pvb_expr = apply_config_on_expression vb.pvb_expr }
      else None)
    vbs

let apply_config_on_signature_items sig_items =
  List.filter_map
    (fun sig_item ->
      match sig_item.psig_desc with
      | Psig_value val_desc ->
          if should_keep val_desc.pval_attributes = `keep then Some sig_item
          else None
      | Psig_type (rec_flag, tds) ->
          let tds = apply_config_on_types tds in
          if List.length tds = 0 then None
          else Some { sig_item with psig_desc = Psig_type (rec_flag, tds) }
      | _ -> Some sig_item)
    sig_items

let apply_config_on_module_type mod_type =
  match mod_type.pmty_desc with
  | Pmty_signature signature_items ->
      let signature_items = apply_config_on_signature_items signature_items in
      { mod_type with pmty_desc = Pmty_signature signature_items }
  | _ -> mod_type

let rec apply_config_on_module_expr mod_expr =
  match mod_expr.pmod_desc with
  | Pmod_apply _ | Pmod_apply_unit _ | Pmod_unpack _ | Pmod_extension _
  | Pmod_ident _ | Pmod_functor _ ->
      mod_expr
  | Pmod_structure structs ->
      let new_structs =
        List.filter_map
          (fun stri ->
            match stri.pstr_desc with
            | Pstr_value (rec_flag, vbs) ->
                let vbs = apply_config_on_value_bindings vbs in
                if List.length vbs = 0 then None
                else Some { stri with pstr_desc = Pstr_value (rec_flag, vbs) }
            | _ -> Some stri)
          structs
      in
      { mod_expr with pmod_desc = Pmod_structure new_structs }
  | Pmod_constraint (module_expr, module_type) ->
      let module_expr = apply_config_on_module_expr module_expr in
      let module_type = apply_config_on_module_type module_type in
      { mod_expr with pmod_desc = Pmod_constraint (module_expr, module_type) }

let apply_config_on_structure_item stri =
  try
    match stri.pstr_desc with
    | Pstr_typext { ptyext_attributes = attrs; _ }
    | Pstr_open { popen_attributes = attrs; _ }
    | Pstr_include { pincl_attributes = attrs; _ }
    | Pstr_exception { ptyexn_attributes = attrs; _ }
    | Pstr_primitive { pval_attributes = attrs; _ }
    | Pstr_eval (_, attrs) ->
        if should_keep attrs = `keep then Some stri else None
    | Pstr_modtype { pmtd_attributes; pmtd_name; pmtd_type; pmtd_loc } ->
        if should_keep pmtd_attributes = `keep then
          match pmtd_type with
          | None -> Some stri
          | Some pmtd_type ->
              let pmtd_type = Some (apply_config_on_module_type pmtd_type) in
              Some
                {
                  stri with
                  pstr_desc =
                    Pstr_modtype
                      { pmtd_attributes; pmtd_name; pmtd_type; pmtd_loc };
                }
        else None
    | Pstr_module { pmb_expr; pmb_name; pmb_attributes; pmb_loc } ->
        if should_keep pmb_attributes = `keep then
          let pmb_expr = apply_config_on_module_expr pmb_expr in
          Some
            {
              stri with
              pstr_desc =
                Pstr_module { pmb_expr; pmb_name; pmb_attributes; pmb_loc };
            }
        else None
    | Pstr_value (recflag, vbs) ->
        if should_keep_many vbs (fun vb -> vb.pvb_attributes) = `keep then
          let vbs = apply_config_on_value_bindings vbs in
          Some { stri with pstr_desc = Pstr_value (recflag, vbs) }
        else None
    | Pstr_type (recflag, tds) ->
        if should_keep_many tds (fun td -> td.ptype_attributes) = `keep then
          let tds = apply_config_on_types tds in
          Some { stri with pstr_desc = Pstr_type (recflag, tds) }
        else None
    | Pstr_recmodule md ->
        if should_keep_many md (fun md -> md.pmb_attributes) = `keep then
          Some stri
        else None
    | Pstr_class cds ->
        if should_keep_many cds (fun cd -> cd.pci_attributes) = `keep then
          Some stri
        else None
    | Pstr_class_type ctds ->
        if should_keep_many ctds (fun ctd -> ctd.pci_attributes) = `keep then
          Some stri
        else None
    | Pstr_extension _ | Pstr_attribute _ -> Some stri
  with Cfg_lang.Error { loc; error } ->
    let ext = Location.error_extensionf ~loc "%s" error in
    Some (Ast_builder.Default.pstr_extension ~loc ext [])

let apply_config_on_signature_item sigi =
  try
    match sigi.psig_desc with
    | Psig_typext { ptyext_attributes = attrs; _ }
    | Psig_modtype { pmtd_attributes = attrs; _ }
    | Psig_open { popen_attributes = attrs; _ }
    | Psig_include { pincl_attributes = attrs; _ }
    | Psig_exception { ptyexn_attributes = attrs; _ }
    | Psig_value { pval_attributes = attrs; _ }
    | Psig_modtypesubst { pmtd_attributes = attrs; _ }
    | Psig_modsubst { pms_attributes = attrs; _ }
    | Psig_module { pmd_attributes = attrs; _ } ->
        if should_keep attrs = `keep then Some sigi else None
    | Psig_typesubst tds ->
        if should_keep_many tds (fun td -> td.ptype_attributes) = `keep then
          let tds = apply_config_on_types tds in
          Some { sigi with psig_desc = Psig_typesubst tds }
        else None
    | Psig_type (recflag, tds) ->
        if should_keep_many tds (fun td -> td.ptype_attributes) = `keep then
          let tds = apply_config_on_types tds in
          Some { sigi with psig_desc = Psig_type (recflag, tds) }
        else None
    | Psig_recmodule md ->
        if should_keep_many md (fun md -> md.pmd_attributes) = `keep then
          Some sigi
        else None
    | Psig_class cds ->
        if should_keep_many cds (fun cd -> cd.pci_attributes) = `keep then
          Some sigi
        else None
    | Psig_class_type ctds ->
        if should_keep_many ctds (fun ctd -> ctd.pci_attributes) = `keep then
          Some sigi
        else None
    | Psig_extension _ | Psig_attribute _ -> Some sigi
  with Cfg_lang.Error { loc; error } ->
    let ext = Location.error_extensionf ~loc "%s" error in
    Some (Ast_builder.Default.psig_extension ~loc ext [])

let preprocess_impl str =
  match str with
  | { pstr_desc = Pstr_attribute attr; _ } :: rest
    when is_config_tag attr.attr_name.txt ->
      if eval_attr attr = `keep then rest else []
  | _ -> List.filter_map apply_config_on_structure_item str

let preprocess_intf sigi =
  match sigi with
  | { psig_desc = Psig_attribute attr; _ } :: rest
    when is_config_tag attr.attr_name.txt ->
      if eval_attr attr = `keep then rest else []
  | _ -> List.filter_map apply_config_on_signature_item sigi

let () =
  Driver.register_transformation tag ~aliases:[ short_tag ] ~preprocess_impl
    ~preprocess_intf
