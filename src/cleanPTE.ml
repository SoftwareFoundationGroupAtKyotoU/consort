open OwnershipInference
module RT = RefinementTypes

type 'a funtype = 'a RT._funtype

(* Whether a given type has ownership 0 *)
let rec is_empty_otype o_map = function
  | Int | TVar _ -> true
  | Array (_, o) | Ref (_, o) | Lock (_, _, o) | ThreadID (_, o) ->
      o_map o = 0.0
  | Tuple tl -> List.for_all (is_empty_otype o_map) tl
  | Mu _ -> failwith "Mu type not supported"

(** Remove variables with ownership 0 in the PTE  *)
let rec clean_otype_with o_map =
  let rec loop = function
    | Lock (pte, lo, ro) ->
        let pte' = clean_pte_with o_map pte in
        Lock (pte', lo, ro)
    | ThreadID (pte, o) ->
        let pte' = clean_pte_with o_map pte in
        ThreadID (pte', o)
    | Tuple tl ->
        let tl' = List.map loop tl in
        Tuple tl'
    | Array (t, o) -> Array (loop t, o)
    | Ref (t, o) -> Ref (loop t, o)
    | (Int | TVar _) as t -> t
    | Mu _ -> failwith "Mu type not supported"
  in
  loop

and clean_pte_with o_map =
  SM.filter_map (fun _ t ->
      if is_empty_otype o_map t then None else Some (clean_otype_with o_map t))

let rec otype_to_simple_type : otype -> SimpleTypes.r_typ = function
  | Int -> `Int
  | TVar i -> `TVar i
  | Ref (t, _) -> `Ref (otype_to_simple_type t)
  | Array (Int, _) -> `Array `Int
  | Tuple tl -> `Tuple (List.map otype_to_simple_type tl)
  | Lock (pte, _, _) -> `Lock (SM.map otype_to_simple_type pte)
  | ThreadID (pte, _) -> `ThreadID (SM.map otype_to_simple_type pte)
  | Mu (_, _) -> failwith "Mu type not supported"
  | Array (_, _) -> failwith "Array elements must be of type int"

let theta_map f theta =
  StringMap.map
    (fun (ft : otype funtype) ->
      let arg_types = List.map f ft.arg_types in
      let output_types = List.map f ft.output_types in
      let result_type = f ft.result_type in
      RT.{ arg_types; output_types; result_type })
    theta

let funtypes_to_funtyps =
  SM.map (fun ({ arg_types; result_type; _ } : SimpleTypes.r_typ funtype) ->
      SimpleTypes.{ arg_types; ret_type = result_type })

(** Remove variables with ownership 0 in the PTE.
    + [tyenvs](type environment) and [theta](function type environment) in [OwnershipInference]
    + [let_types] and function type environment in [SimpleChecker]
*)
let clean ownership_res (simple_theta, simple_results) (infer_res : Result.t) =
  let o_map = function OVar v -> List.assoc v ownership_res | OConst c -> c in
  let clean_otype = clean_otype_with o_map in

  (* For OwnershipInference *)
  let theta = theta_map clean_otype infer_res.theta in
  let ty_envs = Std.IntMap.map (SM.map clean_otype) infer_res.ty_envs in
  let infer_res' = { infer_res with theta; ty_envs } in

  (* For SimpleChecker *)
  let simple_theta' =
    theta
    |> SM.filter (fun name _ -> SM.mem name simple_theta)
       (* Remove intricated types *)
    |> theta_map otype_to_simple_type
    |> funtypes_to_funtyps
  in
  let let_types =
    Std.IntMap.map
      (fun t -> t |> clean_otype |> otype_to_simple_type)
      infer_res.let_types
  in
  let simple_res' : SimpleChecker.simple_results =
    (simple_theta', { simple_results with let_types })
  in

  (simple_res', infer_res')
