open PrettyPrint
open Sexplib.Std
open Format
open Ast

let todo () = assert false

let fn_to_mochi = function
  | "=" -> "eq'"
  | "!=" -> "ne'"
  | "+" -> "( + )"
  | "*" -> "( * )"
  | "-" -> "( - )"
  | "<" -> "lt'"
  | ">" -> "gt'"
  | "<=" -> "le'"
  | ">=" -> "ge'"
  | "%" -> "(mod)"
  | "&&" -> "land'"
  | "||" -> "lor'"
  | fn ->
      if AstPrinter.is_operator_id fn then failwith @@ "Unknown operator " ^ fn
      else fn

let is_builtin_fn = function
  | "=" | "!=" | "+" | "*" | "-" | "<" | ">" | "<=" | ">=" | "%" | "&&" | "||"-> true
  | fn ->
      if AstPrinter.is_operator_id fn then failwith @@ "Unknown operator " ^ fn
      else false

module Mochi = struct
  type adist = Left | Right | Niladist [@@deriving sexp]
  type atype = ABase of adist | ATuple of atype list [@@deriving sexp]

  type exp =
    | Unit
    | Fail
    | Cond of string * exp * exp
    | Let of patt * exp * exp
    | Tuple of exp list
    | Var of string
    | Const of int
    | Call of string * string list
    | Nondet of OwnershipInference.otype * RefinementTypes.refinement option
    | MkArray of string
    | LengthOf of string
    | Read of string * string
    | Assert of relation * exp
    | Update of string * string * string * exp
    | Alias of
        (* Paths.steps list は Paths と逆順 *)
        string
        * string
        * patt
        * patt
        * patt
        * exp
    | Nil
    | Cons of exp * exp
    | Match of string * exp * string * string * exp
  [@@deriving sexp]

  type fn = { name : string; args : string list; body : exp } [@@deriving sexp]
  type prog = fn list * exp [@@deriving sexp]

  let arrfuns =
    "let eq' x y = if x = y then 0 else 1\n\
     let ne' x y = if x <> y then 0 else 1\n\
     let lt' x y = if x < y then 0 else 1\n\
     let gt' x y = if x > y then 0 else 1\n\
     let le' x y = if x <= y then 0 else 1\n\
     let ge' x y = if x >= y then 0 else 1\n\
     let land' x y = if x = 0 && y = 0 then 0 else 1\n\
     let lor' x y = if x = 0 || y = 0 then 0 else 1\n\
     let mkarray' n = (n, fun i -> assert (0 <= i && i < n); 0)\n\
     let update' arr i x = let a = snd arr in (a i; (fst arr, fun j -> a j; if j = i \
     then x else a j))\n"

  let ap_to_string (root, steps, _) =
    let open Paths in
    let pp_root = match root with Var x -> x | _ -> assert false in
    List.fold_left
      (fun acc s ->
        match s with
        | `Deref -> acc
        | `Proj 0 -> acc ^ "fst @@"
        | `Proj 1 -> acc ^ "snd @@"
        | `Cons _ -> assert false
        | _ -> assert false)
      "" steps
    ^ pp_root

  let pp_ap ap = ap_to_string ap |> ps

  let rec pp_refinement r =
    let open RefinementTypes in
    let open Paths in
    match r with
    | Top -> ps "true"
    | ConstEq n -> pf "_' = %d" n
    | Relation { rel_op1; rel_cond; rel_op2 } ->
        let print_rimm ff = function
          | RConst i -> pi i ff
          | RAp c -> pp_ap (c :> root * steps list * suff) ff
        in
        let r1_printer ff r1 =
          match r1 with Nu -> ps "_'" ff | RImm i -> print_rimm ff i
        in
        pf "%a@ %s@ %a" r1_printer rel_op1 rel_cond print_rimm rel_op2
    | And (r1, r2) ->
        pf "%a@ &&@ %a" (ul pp_refinement) r1 (ul pp_refinement) r2
    | _ -> failwith @@ "Cannot annotate with relation " ^ string_of_refinement r

  let rec pp_nondet_ot =
    let open OwnershipInference in
    function
    | Int -> ps "Random.int 0"
    | Tuple ots -> pl [ ps "("; psep ", " @@ List.map pp_nondet_ot ots; ps ")" ]
    | Ref (ot, _) -> pp_nondet_ot ot
    | _ -> assert false

  let rec pp_exp = function
    | Unit -> ps "()"
    | Fail -> ps "Fail"
    | Tuple es -> pl [ ps "("; psep ", " @@ List.map pp_exp es; ps ")" ]
    | Var x ->
        assert (String.get x 0 > 'Z');
        pv x
    | Const i -> pi i
    | Nondet (Int, None) -> ps "Random.int 0"
    | Nondet (Int, Some p) ->
        pf
          "let rec nd' () = @[let _' = Random.int 0 in@;\
           @[if %a then _'@;\
           else nd' ()@;\
           @]@] in nd' ()@;"
          (ul pp_refinement) p
    | Nondet (ot, None) -> pp_nondet_ot ot
    | Nondet (_, _) -> assert false
    | MkArray x -> pf "mkarray' %s" x
    | LengthOf x -> pf "fst %s" x
    | Read (x, i) -> pf "snd %s %s" x i
    | Assert ({ rop1; cond; rop2 }, e) ->
        pl
          [
            pf "assert (%a %s %a)" AstPrinter.upp_imm rop1 cond
              AstPrinter.upp_imm rop2;
            semi;
            pp_exp e;
          ]
    | Update (a, i, x, e) ->
        pl [ pf "let %s = update' %s %s %s in" a a i x; nl; pp_exp e ]
    | Call (callee, arg_names) ->
        let pp_callee = fn_to_mochi callee in
        pf "(%s %s)" pp_callee @@ String.concat " " arg_names
    | Alias (xd, xs, p1, p2, p3, e) ->
        pl
          [
            pf "let %s = %a in" xd (ul pl)
              [
                pf "let %a = %s in" (ul AstPrinter.pp_patt) p1 xd;
                nl;
                pf "let %a = %s in" (ul AstPrinter.pp_patt) p2 xs;
                nl;
                AstPrinter.pp_patt p3;
              ];
            nl;
            pp_exp e;
          ]
    | Cond (x, e1, e2) ->
        pblock ~nl:false ~op:(pf "if %s = 0 then (" x) ~body:(pp_exp e1)
          ~close:
            (pblock ~nl:true ~op:(ps ") else (") ~body:(pp_exp e2)
               ~close:(ps ")"))
    | Let (patt, e1, e2) ->
        pl
          [
            pf "let %a = %a in" (ul AstPrinter.pp_patt) patt (ul pp_exp) e1;
            nl;
            pp_exp e2;
          ]
    | Nil
    | Cons _
    | Match _ -> assert false

  let pp_fn ff { name; args; body } ~first =
    pl
      [
        pblock ~nl:true
          ~op:
            (pf "%s %s %s =" (if first then "let rec" else "and") name
            @@ String.concat " " args)
          ~body:(pp_exp body) ~close:null;
      ]
      ff

  let pp_prog (fn, body) ff =
    pp_open_vbox ff 0;
    List.iteri (fun i -> pp_fn ff ~first:(i = 0)) fn;
    pp_close_box ff ();
    pp_open_vbox ff 1;
    fprintf ff "let main () =@;";
    pp_exp body ff;
    pp_close_box ff ();
    pp_force_newline ff ()

  let print_prog prog =
    print_endline arrfuns;
    pp_prog prog std_formatter
end

let rec lhs_to_mochi (ri : OwnershipInference.Result.t) (ro : (int * float) list) i
    =
  let open OwnershipInference in
  function
  | Var x -> Mochi.Var x
  | Const i -> Mochi.Const i
  | Mkref RNone -> Mochi.Nondet (Int, None)
  | Mkref (RInt i) -> Mochi.Const i
  | Mkref (RVar x) -> Mochi.Var x
  | MkArray x -> Mochi.MkArray x
  | Call { callee; arg_names; _ } -> Mochi.Call (callee, arg_names)
  | Deref x -> (
      (* REVIEW: deref のたびに常に havoc する必要はない *)
      let ty_env = Std.IntMap.find i ri.ty_envs in
      let ty = StringMap.find x ty_env in
      match ty with
      | Ref (t, o) ->
          let r = match o with OConst r -> r | OVar i -> List.assoc i ro in
          if r > 0. then Mochi.Var x else Mochi.Nondet (t, None)
      | _ -> raise @@ Failure "illegal deref")
  | Tuple ls ->
      Mochi.(
        Tuple
          (List.map
             (function
               | RNone -> Nondet (Int, None)
               | RInt i -> Const i
               | RVar x -> Var x)
             ls))
  | Nondet p -> Mochi.Nondet (Int, p)
  | LengthOf x -> Mochi.LengthOf x
  | Read (x, y) -> Mochi.Read (x, y)
  | Null -> raise @@ Failure "null is not supported"
  | Nil -> Mochi.Nil
  | Cons (h, t) -> Mochi.Cons (lhs_to_mochi ri ro i h, lhs_to_mochi ri ro i t)

let map_o ro o =
  let open OwnershipInference in
  match o with OConst r -> r | OVar i -> List.assoc i ro

let alias_to_adist (ro : (int * float) list)
    ((tl, sl) : OwnershipInference.otype * Paths.steps list)
    ((tr, sr) : OwnershipInference.otype * Paths.steps list) =
  let open OwnershipInference in
  let rsl = List.rev sl in
  let rsr = List.rev sr in
  let rec walk ty = function
    | [] -> ty
    | `Deref :: ss -> (
        match ty with
        | Ref (ty', o) ->
            (* WF より, オーナーシップ0の先をエイリアス宣言しても意味ない *)
            assert (map_o ro o > 0.);
            walk ty' ss
        | _ -> assert false)
    | `Proj i :: ss -> (
        match ty with
        | Tuple tys -> walk (List.nth tys i) ss
        | _ -> assert false)
    | `Cons _ :: _ -> assert false
  in
  let tl = walk tl rsl in
  let tr = walk tr rsr in
  let open Mochi in
  let rec loop tl tr =
    match (tl, tr) with
    | Array (tl', o1), Array (tr', o2) | Ref (tl', o1), Ref (tr', o2) ->
        let zl, zr = (map_o ro o1 = 0., map_o ro o2 = 0.) in
        if zl then if zr then Niladist else Left
        else if zr then Right
        else loop tl' tr'
    | Tuple tsl, Tuple tsr ->
        let adists = List.map2 loop tsl tsr in
        let nl, nr, nn =
          List.fold_left
            (fun (nl, nr, nn) -> function
              | Left -> (nl + 1, nr, nn)
              | Right -> (nl, nr + 1, nn)
              | Niladist -> (nl, nr, nn + 1))
            (0, 0, 0) adists
        in
        let n = List.length adists in
        if nn = n then Niladist
        else if nl + nn = n then Left
        else if nr + nn = n then Right
        else assert false
    | Int, Int -> Niladist
    | t1, _ ->
        failwith
          (Printf.sprintf "ill type: %s" (sexp_of_otype t1 |> string_of_sexp))
  in
  (rsl, rsr, loop tl tr)

let alias_to_patt (ro : (int * float) list)
    ((xl, tl, sl) : string * OwnershipInference.otype * Paths.steps list)
    ((xr, tr, sr) : string * OwnershipInference.otype * Paths.steps list) =
  let open OwnershipInference in
  let rsl, rsr, adist = alias_to_adist ro (tl, sl) (tr, sr) in
  let xd, td, sd, xs, ts, ss =
    match adist with
    | Left -> (xl, tl, rsl, xr, tr, rsr)
    | _ -> (xr, tr, rsr, xl, tl, rsl)
  in
  let rec xname x = function
    | [] -> x
    | `Deref :: s -> xname x s
    | `Proj i :: s -> xname (Printf.sprintf "%s'%i" x i) s
    | `Cons _ :: _ -> assert false
  in
  let xxd = xname xd sd in
  let xxs = xname xs ss in
  let rec e_patt rx x t = function
    | [] -> PVar rx
    | `Deref :: s -> (
        match t with
        | Ref (t', o) ->
            assert (map_o ro o > 0.);
            e_patt rx x t' s
        | _ -> assert false)
    | `Proj i :: s -> (
        match t with
        | Tuple tys ->
            let x' = Printf.sprintf "%s'%i" x i in
            PTuple
              (List.mapi
                 (fun j ty -> if i = j then e_patt rx x' ty s else PVar x')
                 tys)
        | _ -> assert false)
    | `Cons _ :: _ -> assert false
  in
  let ptd = e_patt xxd xd td sd in
  let pts = e_patt xxs xs ts ss in
  let pt_ = e_patt xxs xd td sd in
  (xd, xs, ptd, pts, pt_)
(*
let alias_to_aty (ro : (int * float) list)
    ((tl, sl) : OwnershipInference.otype * Paths.steps list)
    ((tr, sr) : OwnershipInference.otype * Paths.steps list) =
  let open OwnershipInference in
  let rsl = List.rev sl in
  let rsr = List.rev sr in
  let rec walk ty = function
    | [] -> ty
    | `Deref :: ss -> (
        match ty with
        | Ref (ty', o) ->
            assert (map_o ro o > 0.);
            walk ty' ss
        | _ -> assert false)
    | `Proj i :: ss -> (
        match ty with
        | Tuple tys -> walk (List.nth tys i) ss
        | _ -> assert false)
  in
  let tl = walk tl rsl in
  let tr = walk tr rsr in
  let open Mochi in
  let rec loop tl tr =
    match (tl, tr) with
    | Array (tl', o1), Array (tr', o2) | Ref (tl', o1), Ref (tr', o2) ->
        let zl, zr = (map_o ro o1 = 0., map_o ro o2 = 0.) in
        if zl then if zr then ABase Nil else ABase Left
        else if zr then ABase Right
        else loop tl' tr'
    | Tuple tsl, Tuple tsr ->
        let atys = List.map2 loop tsl tsr in
        let nl, nr, nn =
          List.fold_left
            (fun ((nl, nr, nn) as acc) -> function
              | ABase Left -> (nl + 1, nr, nn)
              | ABase Right -> (nl, nr + 1, nn)
              | ABase Nil -> (nl, nr, nn + 1)
              | _ -> acc)
            (0, 0, 0) atys
        in
        let n = List.length atys in
        if nl = n then ABase Left
        else if nr = n then ABase Right
        else if nn = n then ABase Nil
        else ATuple atys
    | Int, Int -> ABase Nil
    | _ -> assert false
  in
  loop tl tr *)

let rec exp_to_mochi (ri : OwnershipInference.Result.t)
    (ro : (int * float) list) (vs : string list) (((i, _), e) : exp) =
  let map_ty x =
    let ty_env = Std.IntMap.find i ri.ty_envs in
    StringMap.find x ty_env
  in
  match e with
  | Unit -> Mochi.(Tuple (Unit :: List.map (fun v -> Var v) vs))
  | Cond (x, e1, e2) ->
      Mochi.Cond (x, exp_to_mochi ri ro vs e1, exp_to_mochi ri ro vs e2)
  | Seq ((((i', _), _) as e1), e2) ->
      let vs' =
        StringMap.fold
          (fun v _ vs -> v :: vs)
          (Std.IntMap.find i' ri.ty_envs)
          []
      in
      Mochi.(
        Let
          ( PTuple (PNone :: List.map (fun v -> PVar v) vs'),
            exp_to_mochi ri ro vs' e1,
            exp_to_mochi ri ro vs e2 ))
  | Assign (x, iv, e) ->
      let e' =
        match iv with IVar y -> Mochi.Var y | IInt i -> Mochi.Const i
      in
      Mochi.(Let (PVar x, e', exp_to_mochi ri ro vs e))
  | Return x -> Mochi.(Tuple (Var x :: List.map (fun v -> Var v) vs))
  | Let (patt, (Call { callee; arg_names; _ } as lhs), e)
    when not @@ is_builtin_fn callee ->
      Mochi.Let
        ( PTuple (patt :: List.map (fun x -> PVar x) arg_names),
          lhs_to_mochi ri ro i lhs,
          exp_to_mochi ri ro vs e )
  | Let (patt, lhs, e) ->
      Mochi.Let (patt, lhs_to_mochi ri ro i lhs, exp_to_mochi ri ro vs e)
  | NCond (_, _, _) -> raise @@ Failure "null is not supported"
  | Fail -> Mochi.Fail
  | Assert (p, e) -> Mochi.Assert (p, exp_to_mochi ri ro vs e)
  | Update (a, i, x, e) -> Mochi.Update (a, i, x, exp_to_mochi ri ro vs e)
  | Alias (p1, p2, e) -> (
      let open Paths in
      let r1, st1, _ = (p1 :> root * steps list * suff) in
      let r2, st2, _ = (p2 :> root * steps list * suff) in
      match (r1, r2) with
      | Var x1, Var x2 ->
          let xd, xs, p1, p2, p3 =
            alias_to_patt ro (x1, map_ty x1, st1) (x2, map_ty x2, st2)
          in
          Mochi.Alias (xd, xs, p1, p2, p3, exp_to_mochi ri ro vs e)
      | _ -> assert false)
  | Match (e1, e2, h, t, e3) ->
    match e1 with
      Var x -> Mochi.Match (x, exp_to_mochi ri ro vs e2, h, t, exp_to_mochi ri ro vs e3)
    | _ -> failwith "Not implemented"

let fn_to_mochi (ri : OwnershipInference.Result.t) (ro : (int * float) list)
    { name; args; body } =
  Mochi.{ name; args; body = exp_to_mochi ri ro args body }

let prog_to_mochi (ri : OwnershipInference.Result.t) (ro : (int * float) list)
    (fns, exp) =
  (List.map (fn_to_mochi ri ro) fns, exp_to_mochi ri ro [] exp)
