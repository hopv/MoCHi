open Util
open Type

type label = Read | Write | Close
and binop = Eq | Lt | Gt | Leq | Geq | And | Or | Add | Sub | Mult | Div

and typ = term Type.t
and tattr = term Type.attr [@printer Type.print_attr]
and id = typ Id.t

and const = (* only base type constants *)
  | Unit
  | True
  | False
  | Int of int
  | Char of char
  | String of string
  | Float of float
  | Int32 of int32
  | Int64 of int64
  | Nativeint of nativeint
  | CPS_result
  | Rand of typ * bool (** true denotes CPS-term *)
  | Empty

and attr =
  | AAbst_under
  | ATerminate
  | ANotFail
  | ADeterministic
  | AComment of string
  | AId of int
  | ADoNotInline
  | AEffect of Type.effect list
  | ALoc of (Location.t [@printer (fun _ _ -> ())])
  | AMark of bool ref
  | AInfo of info (** temporal information for transformations *)

and term = {desc:desc; typ:typ; attr:attr list}
and desc =
  | End_of_definitions
  | Const of const
  | Var of id
  | Fun of id * term
  | App of term * term list
  | If of term * term * term
  | Local of declaration * term
  | BinOp of binop * term * term
  | Not of term
  | Event of string * bool (** true denotes CPS-term *)
  | Record of (string * term) list
  | Field of term * string
  | SetField of term * string * term
  | Nil
  | Cons of term * term
  | Constr of string * term list
  | Match of term * (pattern * term) list (** a term diverges if no patters are matched *)
  | Raise of term
  | TryWith of term * term
  | Tuple of term list
  | Proj of int * term
  | Bottom
  | Label of info * term (* just for tupling? *)
  | Ref of term
  | Deref of term
  | SetRef of term * term
  | TNone
  | TSome of term
  | Module of declaration list
  | MemSet of term * term (** MemSet(x,X) means x \in X *)
  | AddSet of term * term (** AddSet(x,X) means {x} \cup X *)
  | Subset of term * term (** SubSet(X,Y) means X \subset Y *)

and declaration =
  | Decl_let of (id * term) list
  | Decl_type of (string * typ) list
  | Open of id

and info =
  | InfoInt of int
  | InfoString of string
  | InfoId of id
  | InfoTerm of term
  | InfoIdTerm of id * term


and type_kind =
  | KAbstract
  | KVariant of (string * typ list) list
  | KRecord of (string * (mutable_flag * typ)) list
  | KOpen

and rec_flag = Nonrecursive | Recursive

and pred = desc

and pattern = {pat_desc:pat_desc; pat_typ:typ}
and pat_desc =
  | PAny
  | PNondet (* match non-deterministically: can be replaced with PWhen *)
  | PVar of id
  | PAlias of pattern * id
  | PConst of term
  | PConstr of string * pattern list
  | PNil
  | PCons of pattern * pattern
  | PTuple of pattern list
  | PRecord of (string * pattern) list
  | PNone
  | PSome of pattern
  | POr of pattern * pattern
  | PWhen of pattern * term
  [@@deriving show]

type env = (id * typ) list

let typ t = t.typ
let desc t = t.desc
let attr t = t.attr


module Id = struct
  include Id
  let new_var ?name ?(attr=[]) typ =
    let name =
      match name with
      | None -> Type.var_name_of typ
      | Some name -> name
    in
    make !!new_int name attr typ
end

module ID = struct
  type t = id
  let compare = Id.compare
  let print = Id.print
end

module PredVar = struct
  let pvar_name = "P"
  let is_pvar = Id.is_predicate
  let new_pvar ?(name=pvar_name) tys =
    let ty = List.fold_right make_tfun tys Ty.bool in
    Id.new_var ~name ~attr:[Id.Predicate] ty
end


let safe_attr = [ANotFail;ATerminate]
let pure_attr = [ANotFail; ATerminate; ADeterministic]
let const_attr = pure_attr

type trans =
  {mutable tr_term:      term -> term;
   mutable tr_term_rec:  term -> term;
   mutable tr_desc:      desc -> desc;
   mutable tr_desc_rec:  desc -> desc;
   mutable tr_typ:       typ -> typ;
   mutable tr_typ_rec:   typ -> typ;
   mutable tr_var:       id -> id;
   mutable tr_var_rec:   id -> id;
   mutable tr_pat:       pattern -> pattern;
   mutable tr_pat_rec:   pattern -> pattern;
   mutable tr_info:      info -> info;
   mutable tr_info_rec:  info -> info;
   mutable tr_decl:      declaration -> declaration;
   mutable tr_decl_rec:  declaration -> declaration;
   mutable tr_const:     const -> const;
   mutable tr_const_rec: const -> const;
   mutable tr_attr:      attr list -> attr list}

let trans_typ tr = function
  | TBase b -> TBase b
  | TVar({contents=None} as x,id) -> TVar(x,id)
  | TVar({contents=Some typ},_) -> tr.tr_typ typ
  | TFun(x,typ) -> TFun(Id.map_typ tr.tr_typ x, tr.tr_typ typ)
  | TFuns(xs,typ) -> TFuns(List.map (Id.map_typ tr.tr_typ) xs, tr.tr_typ typ)
  | TApp(c, typs) -> TApp(c, List.map tr.tr_typ typs)
  | TTuple xs -> TTuple (List.map tr.tr_var xs)
  | TData s -> TData s
  | TAttr(attr, typ) ->
      let tr_attr a =
        match a with
        | TAPred(x,ps) -> TAPred(tr.tr_var x, List.map tr.tr_term ps)
        | TARefPred(x,p) -> TARefPred(tr.tr_var x, tr.tr_term p)
        | TAPureFun -> TAPureFun
        | TAEffect e -> TAEffect e
        | TAPredShare x -> TAPredShare x
        | TAId(s,n) -> TAId(s,n)
        | TARaise ty -> TARaise (tr.tr_typ ty)
      in
      TAttr(List.map tr_attr attr, tr.tr_typ typ)
  | TVariant(poly,labels) -> TVariant(poly, List.map (Pair.map_snd @@ List.map tr.tr_typ) labels)
  | TRecord fields -> TRecord (List.map (Pair.map_snd @@ Pair.map_snd tr.tr_typ) fields)
  | TModule {sig_types; sig_values} ->
      let sig_types = List.map (Pair.map_snd tr.tr_typ) sig_types in
      let sig_values = List.map tr.tr_var sig_values in
      TModule {sig_types; sig_values}

let trans_var tr x = Id.map_typ tr.tr_typ x

let trans_pat tr p =
  let typ = tr.tr_typ p.pat_typ in
  let desc =
    match p.pat_desc with
    | PAny -> PAny
    | PNondet -> PNondet
    | PVar x -> PVar (tr.tr_var x)
    | PAlias(p,x) -> PAlias(tr.tr_pat p, tr.tr_var x)
    | PConst t -> PConst (tr.tr_term t)
    | PConstr(s,ps) -> PConstr(s, List.map tr.tr_pat ps)
    | PNil -> PNil
    | PCons(p1,p2) -> PCons(tr.tr_pat p1, tr.tr_pat p2)
    | PTuple ps -> PTuple (List.map tr.tr_pat ps)
    | PRecord pats -> PRecord(List.map (Pair.map_snd tr.tr_pat) pats)
    | POr(p1,p2) -> POr(tr.tr_pat p1, tr.tr_pat p2)
    | PNone -> PNone
    | PSome p -> PSome (tr.tr_pat p)
    | PWhen(p,cond) -> PWhen(tr.tr_pat p, tr.tr_term cond)
  in
  {pat_desc=desc; pat_typ=typ}

let trans_info tr = function
  | InfoInt n -> InfoInt n
  | InfoString s -> InfoString s
  | InfoId x -> InfoId (tr.tr_var x)
  | InfoTerm t -> InfoTerm (tr.tr_term t)
  | InfoIdTerm(x, t) ->  InfoIdTerm(tr.tr_var x, tr.tr_term t)

let trans_const tr c =
  match c with
  | Unit -> Unit
  | True -> True
  | False -> False
  | Int n -> Int n
  | Char c -> Char c
  | String s -> String s
  | Float s -> Float s
  | Int32 n -> Int32 n
  | Int64 n -> Int64 n
  | Nativeint n -> Nativeint n
  | CPS_result -> CPS_result
  | Rand(typ,b) -> Rand(tr.tr_typ typ,b)
  | Empty -> Empty

let trans_decl tr decl =
  match decl with
  | Decl_let defs -> Decl_let (List.map (Pair.map tr.tr_var tr.tr_term) defs)
  | Decl_type decls -> Decl_type (List.map (Pair.map_snd tr.tr_typ) decls)
  | Open m -> Open (tr.tr_var m)

let trans_desc tr = function
  | End_of_definitions -> End_of_definitions
  | Const c -> Const(tr.tr_const c)
  | Var y -> Var (tr.tr_var y)
  | Fun(y, t) -> Fun(tr.tr_var y, tr.tr_term t)
  | App(t1, ts) -> App(tr.tr_term t1, List.map tr.tr_term ts)
  | If(t1, t2, t3) -> If(tr.tr_term t1, tr.tr_term t2, tr.tr_term t3)
  | Local(decl, t2) -> Local(tr.tr_decl decl, tr.tr_term t2)
  | BinOp(op, t1, t2) -> BinOp(op, tr.tr_term t1, tr.tr_term t2)
  | Not t1 -> Not (tr.tr_term t1)
  | Event(s,b) -> Event(s,b)
  | Record fields ->  Record (List.map (Pair.map_snd tr.tr_term) fields)
  | Field(t1,s) -> Field(tr.tr_term t1, s)
  | SetField(t1,s,t2) -> SetField(tr.tr_term t1,s,tr.tr_term t2)
  | Nil -> Nil
  | Cons(t1,t2) -> Cons(tr.tr_term t1, tr.tr_term t2)
  | Constr(s,ts) -> Constr(s, List.map tr.tr_term ts)
  | Match(t1,pats) -> Match(tr.tr_term t1, List.map (Pair.map tr.tr_pat tr.tr_term) pats)
  | Raise t -> Raise (tr.tr_term t)
  | TryWith(t1,t2) -> TryWith(tr.tr_term t1, tr.tr_term t2)
  | Tuple ts -> Tuple (List.map tr.tr_term ts)
  | Proj(i,t) -> Proj(i, tr.tr_term t)
  | Bottom -> Bottom
  | Label(info, t) -> Label(tr.tr_info info, tr.tr_term t)
  | Ref t -> Ref(tr.tr_term t)
  | Deref t -> Deref(tr.tr_term t)
  | SetRef(t1, t2) -> SetRef(tr.tr_term t1, tr.tr_term t2)
  | TNone -> TNone
  | TSome t -> TSome (tr.tr_term t)
  | Module decls -> Module (List.map tr.tr_decl decls)
  | MemSet(t1, t2) -> MemSet(tr.tr_term t1, tr.tr_term t2)
  | AddSet(t1, t2) -> AddSet(tr.tr_term t1, tr.tr_term t2)
  | Subset(t1, t2) -> Subset(tr.tr_term t1, tr.tr_term t2)

let trans_term tr t =
  {desc = tr.tr_desc t.desc; typ = tr.tr_typ t.typ; attr=tr.tr_attr t.attr}



let make_trans () =
  let tr =
    {tr_term = Fun.id;
     tr_term_rec = Fun.id;
     tr_desc = Fun.id;
     tr_desc_rec = Fun.id;
     tr_typ = Fun.id;
     tr_typ_rec = Fun.id;
     tr_var = Fun.id;
     tr_var_rec = Fun.id;
     tr_pat = Fun.id;
     tr_pat_rec = Fun.id;
     tr_info = Fun.id;
     tr_info_rec = Fun.id;
     tr_const = Fun.id;
     tr_const_rec = Fun.id;
     tr_decl = Fun.id;
     tr_decl_rec = Fun.id;
     tr_attr = Fun.id}
  in
  tr.tr_term <- trans_term tr;
  tr.tr_term_rec <- trans_term tr;
  tr.tr_desc <- trans_desc tr;
  tr.tr_desc_rec <- trans_desc tr;
  tr.tr_typ <- trans_typ tr;
  tr.tr_typ_rec <- trans_typ tr;
  tr.tr_var <- trans_var tr;
  tr.tr_var_rec <- trans_var tr;
  tr.tr_pat <- trans_pat tr;
  tr.tr_pat_rec <- trans_pat tr;
  tr.tr_info <- trans_info tr;
  tr.tr_info_rec <- trans_info tr;
  tr.tr_const <- trans_const tr;
  tr.tr_const_rec <- trans_const tr;
  tr.tr_decl <- trans_decl tr;
  tr.tr_decl_rec <- trans_decl tr;
  tr







type 'a trans2 =
  {mutable tr2_term: 'a -> term -> term;
   mutable tr2_term_rec: 'a -> term -> term;
   mutable tr2_desc: 'a -> desc -> desc;
   mutable tr2_desc_rec: 'a -> desc -> desc;
   mutable tr2_typ: 'a -> typ -> typ;
   mutable tr2_typ_rec: 'a -> typ -> typ;
   mutable tr2_var: 'a -> id -> id;
   mutable tr2_var_rec: 'a -> id -> id;
   mutable tr2_pat: 'a -> pattern -> pattern;
   mutable tr2_pat_rec: 'a -> pattern -> pattern;
   mutable tr2_info: 'a -> info -> info;
   mutable tr2_info_rec: 'a -> info -> info;
   mutable tr2_decl: 'a -> declaration -> declaration;
   mutable tr2_decl_rec: 'a -> declaration -> declaration;
   mutable tr2_const: 'a -> const -> const;
   mutable tr2_const_rec: 'a -> const -> const;
   mutable tr2_attr: 'a -> attr list -> attr list}

let trans2_gen_typ tr env = function
  | TBase b -> TBase b
  | TVar({contents=None} as x,id) -> TVar(x,id)
  | TVar({contents=Some typ},_) -> tr.tr2_typ env typ
  | TFun(x,typ) -> TFun(Id.map_typ (tr.tr2_typ env) x, tr.tr2_typ env typ)
  | TFuns(xs,typ) -> TFuns(List.map (Id.map_typ @@ tr.tr2_typ env) xs, tr.tr2_typ env typ)
  | TApp(c, typs) -> TApp(c, List.map (tr.tr2_typ env) typs)
  | TTuple xs -> TTuple (List.map (tr.tr2_var env) xs)
  | TData s -> TData s
  | TAttr(attr, typ) ->
      let aux a =
        match a with
        | TAPred(x,ps) -> TAPred(tr.tr2_var env x, List.map (tr.tr2_term env) ps)
        | TARefPred(x,p) -> TARefPred(tr.tr2_var env x, tr.tr2_term env p)
        | TAPureFun -> TAPureFun
        | TAEffect e -> TAEffect e
        | TAPredShare x -> TAPredShare x
        | TAId(s,n) -> TAId(s,n)
        | TARaise ty -> TARaise (tr.tr2_typ env ty)
      in
      TAttr(List.map aux attr, tr.tr2_typ env typ)
  | TVariant(poly,labels) -> TVariant(poly, List.map (Pair.map_snd @@ List.map @@ tr.tr2_typ env) labels)
  | TRecord fields -> TRecord (List.map (Pair.map_snd @@ Pair.map_snd @@ tr.tr2_typ env) fields)
  | TModule {sig_types; sig_values} ->
      let sig_types = List.map (Pair.map_snd @@ tr.tr2_typ env) sig_types in
      let sig_values = List.map (tr.tr2_var env) sig_values in
      TModule {sig_types; sig_values}


let trans2_gen_var tr env x = Id.map_typ (tr.tr2_typ env) x

let trans2_gen_pat tr env p =
  let typ = tr.tr2_typ env p.pat_typ in
  let desc =
    match p.pat_desc with
    | PAny -> PAny
    | PNondet -> PNondet
    | PVar x -> PVar (tr.tr2_var env x)
    | PAlias(p,x) -> PAlias(tr.tr2_pat env p, tr.tr2_var env x)
    | PConst t -> PConst (tr.tr2_term env t)
    | PConstr(s,ps) -> PConstr(s, List.map (tr.tr2_pat env) ps)
    | PNil -> PNil
    | PCons(p1,p2) -> PCons(tr.tr2_pat env p1, tr.tr2_pat env p2)
    | PTuple ps -> PTuple (List.map (tr.tr2_pat env) ps)
    | PRecord pats -> PRecord(List.map (Pair.map_snd @@ tr.tr2_pat env) pats)
    | POr(p1,p2) -> POr(tr.tr2_pat env p1, tr.tr2_pat env p2)
    | PNone -> PNone
    | PSome p -> PSome (tr.tr2_pat env p)
    | PWhen(p,cond) -> PWhen(tr.tr2_pat env p, tr.tr2_term env cond)
  in
  {pat_desc=desc; pat_typ=typ}

let trans2_gen_info tr env = function
  | InfoInt n -> InfoInt n
  | InfoString s -> InfoString s
  | InfoId x -> InfoId (tr.tr2_var env x)
  | InfoTerm t -> InfoTerm (tr.tr2_term env t)
  | InfoIdTerm(x, t) -> InfoIdTerm(tr.tr2_var env x, tr.tr2_term env t)

let trans2_gen_const tr env c =
  match c with
  | Unit -> Unit
  | True -> True
  | False -> False
  | Int n -> Int n
  | Char c -> Char c
  | String s -> String s
  | Float s -> Float s
  | Int32 n -> Int32 n
  | Int64 n -> Int64 n
  | Nativeint n -> Nativeint n
  | CPS_result -> CPS_result
  | Rand(typ,b) -> Rand(tr.tr2_typ env typ, b)
  | Empty -> Empty

let trans2_gen_decl tr env decl =
  match decl with
  | Decl_let defs -> Decl_let (List.map (Pair.map (tr.tr2_var env) (tr.tr2_term env)) defs)
  | Decl_type decls -> Decl_type (List.map (Pair.map_snd @@ tr.tr2_typ env) decls)
  | Open m -> Open (tr.tr2_var env m)

let trans2_gen_desc tr env desc =
  match desc with
  | End_of_definitions -> End_of_definitions
  | Const c -> Const(tr.tr2_const env c)
  | Var y -> Var (tr.tr2_var env y)
  | Fun(y, t) -> Fun(tr.tr2_var env y, tr.tr2_term env t)
  | App(t1, ts) -> App(tr.tr2_term env t1, List.map (tr.tr2_term env) ts)
  | If(t1, t2, t3) -> If(tr.tr2_term env t1, tr.tr2_term env t2, tr.tr2_term env t3)
  | Local(decl, t2) -> Local(tr.tr2_decl env decl, tr.tr2_term env t2)
  | BinOp(op, t1, t2) -> BinOp(op, tr.tr2_term env t1, tr.tr2_term env t2)
  | Not t1 -> Not (tr.tr2_term env t1)
  | Event(s,b) -> Event(s,b)
  | Record fields -> Record (List.map (Pair.map_snd @@ tr.tr2_term env) fields)
  | Field(t1,s) -> Field(tr.tr2_term env t1,s)
  | SetField(t1,s,t2) -> SetField(tr.tr2_term env t1,s,tr.tr2_term env t2)
  | Nil -> Nil
  | Cons(t1,t2) -> Cons(tr.tr2_term env t1, tr.tr2_term env t2)
  | Constr(s,ts) -> Constr(s, List.map (tr.tr2_term env) ts)
  | Match(t1,pats) ->
      Match(tr.tr2_term env t1, List.map (Pair.map (tr.tr2_pat env) (tr.tr2_term env)) pats)
  | Raise t -> Raise (tr.tr2_term env t)
  | TryWith(t1,t2) -> TryWith(tr.tr2_term env t1, tr.tr2_term env t2)
  | Tuple ts -> Tuple (List.map (tr.tr2_term env) ts)
  | Proj(i,t) -> Proj(i, tr.tr2_term env t)
  | Bottom -> Bottom
  | Label(info, t) -> Label(tr.tr2_info env info, tr.tr2_term env t)
  | Ref t -> Ref (tr.tr2_term env t)
  | Deref t -> Deref (tr.tr2_term env t)
  | SetRef(t1,t2) -> SetRef(tr.tr2_term env t1, tr.tr2_term env t2)
  | TNone -> TNone
  | TSome t -> TSome (tr.tr2_term env t)
  | Module decls -> Module (List.map (tr.tr2_decl env) decls)
  | MemSet(t1, t2) -> MemSet(tr.tr2_term env t1, tr.tr2_term env t2)
  | AddSet(t1, t2) -> AddSet(tr.tr2_term env t1, tr.tr2_term env t2)
  | Subset(t1, t2) -> Subset(tr.tr2_term env t1, tr.tr2_term env t2)

let trans2_gen_term tr env t = {desc = tr.tr2_desc env t.desc; typ = tr.tr2_typ env t.typ; attr = tr.tr2_attr env t.attr}


let make_trans2 () =
  let id' _ = Fun.id in
  let tr =
    {tr2_term = id';
     tr2_term_rec = id';
     tr2_desc = id';
     tr2_desc_rec = id';
     tr2_typ = id';
     tr2_typ_rec = id';
     tr2_var = id';
     tr2_var_rec = id';
     tr2_pat = id';
     tr2_pat_rec = id';
     tr2_info = id';
     tr2_info_rec = id';
     tr2_decl = id';
     tr2_decl_rec = id';
     tr2_const = id';
     tr2_const_rec = id';
     tr2_attr = id'}
  in
  tr.tr2_term <- trans2_gen_term tr;
  tr.tr2_term_rec <- trans2_gen_term tr;
  tr.tr2_desc <- trans2_gen_desc tr;
  tr.tr2_desc_rec <- trans2_gen_desc tr;
  tr.tr2_typ <- trans2_gen_typ tr;
  tr.tr2_typ_rec <- trans2_gen_typ tr;
  tr.tr2_var <- trans2_gen_var tr;
  tr.tr2_var_rec <- trans2_gen_var tr;
  tr.tr2_pat <- trans2_gen_pat tr;
  tr.tr2_pat_rec <- trans2_gen_pat tr;
  tr.tr2_info <- trans2_gen_info tr;
  tr.tr2_info_rec <- trans2_gen_info tr;
  tr.tr2_decl <- trans2_gen_decl tr;
  tr.tr2_decl_rec <- trans2_gen_decl tr;
  tr.tr2_const <- trans2_gen_const tr;
  tr.tr2_const_rec <- trans2_gen_const tr;
  tr






type 'a col =
  {mutable col_term: term -> 'a;
   mutable col_term_rec: term -> 'a;
   mutable col_desc: desc -> 'a;
   mutable col_desc_rec: desc -> 'a;
   mutable col_typ: typ -> 'a;
   mutable col_typ_rec: typ -> 'a;
   mutable col_var: id -> 'a;
   mutable col_var_rec: id -> 'a;
   mutable col_pat: pattern -> 'a;
   mutable col_pat_rec: pattern -> 'a;
   mutable col_info: info -> 'a;
   mutable col_info_rec: info -> 'a;
   mutable col_decl: declaration -> 'a;
   mutable col_decl_rec: declaration -> 'a;
   mutable col_const: const -> 'a;
   mutable col_const_rec: const -> 'a;
   mutable col_attr: attr list -> 'a;
   mutable col_app: 'a -> 'a -> 'a;
   mutable col_empty: 'a}

let col_list col ?(init=col.col_empty) f xs =
  List.fold_left (fun acc typ -> col.col_app acc @@ f typ) init xs

let col_typ col typ =
  let (++) = col.col_app in
  match typ with
  | TBase _ -> col.col_empty
  | TVar({contents=None},_) -> col.col_empty
  | TVar({contents=Some typ},_) -> col.col_typ typ
  | TFun(x,typ) -> col.col_typ (Id.typ x) ++ col.col_typ typ
  | TFuns(xs,typ) -> col_list col ~init:(col.col_typ typ) col.col_var xs
  | TApp(_, typs) -> col_list col col.col_typ typs
  | TTuple xs -> col_list col col.col_var xs
  | TData _ -> col.col_empty
  | TAttr(attr, typ) ->
      let aux acc a =
        match a with
        | TAPred(x,ps) ->
            let acc' = col.col_var x ++ acc in
            List.fold_left (fun acc p -> acc ++ col.col_term p) acc' ps
        | TARefPred(x,p) -> col.col_var x ++ col.col_term p ++ acc
        | TAPureFun -> acc
        | TAEffect _ -> acc
        | TAPredShare _ -> acc
        | TAId _ -> acc
        | TARaise ty -> col.col_typ ty ++ acc
      in
      List.fold_left aux (col.col_typ typ) attr
  | TVariant(_,labels) -> List.fold_left (fun init (_,typs) -> col_list col col.col_typ ~init typs) col.col_empty labels
  | TRecord fields -> col_list col (snd |- snd |- col.col_typ) fields
  | TModule {sig_types; sig_values} ->
      col_list col (snd |- col.col_typ) sig_types ++ col_list col col.col_var sig_values

let col_var col x = col.col_typ (Id.typ x)

let col_pat col p =
  let (++) = col.col_app in
  let r1 = col.col_typ p.pat_typ in
  let r2 =
    match p.pat_desc with
    | PAny -> col.col_empty
    | PNondet -> col.col_empty
    | PVar x -> col.col_var x
    | PAlias(p,x) -> col.col_pat p ++ col.col_var x
    | PConst t -> col.col_term t
    | PConstr(_,ps) -> col_list col col.col_pat ps
    | PNil -> col.col_empty
    | PCons(p1,p2) -> col.col_pat p1 ++ col.col_pat p2
    | PTuple ps -> col_list col col.col_pat ps
    | PRecord pats -> col_list col (snd |- col.col_pat) pats
    | POr(p1,p2) -> col.col_pat p1 ++ col.col_pat p2
    | PNone -> col.col_empty
    | PSome p -> col.col_pat p
    | PWhen(p,cond) -> col.col_pat p ++ col.col_term cond
  in
  col.col_app r1 r2

let col_info col info =
  match info with
  | InfoInt _ -> col.col_empty
  | InfoString _ -> col.col_empty
  | InfoId x -> col.col_var x
  | InfoTerm t -> col.col_term t
  | InfoIdTerm(x, t) -> col.col_app (col.col_var x) (col.col_term t)

let col_const col c =
  match c with
  | Rand(typ,_) -> col.col_typ typ
  | _ -> col.col_empty

let col_decl col decl =
  match decl with
  | Decl_let defs ->
      let aux acc (x,t) =
        col.col_app acc @@
        col.col_app (col.col_var x) (col.col_term t)
      in
      List.fold_left aux col.col_empty defs
  | Decl_type decls -> col_list col (snd |- col.col_typ) decls
  | Open m -> col.col_var m

let col_desc col desc =
  let (++) = col.col_app in
  match desc with
  | End_of_definitions -> col.col_empty
  | Const c -> col.col_const c
  | Var y -> col.col_var y
  | Fun(y, t) -> col.col_var y ++ col.col_term t
  | App(t1, ts) -> col_list col col.col_term ~init:(col.col_term t1) ts
  | If(t1, t2, t3) -> col.col_term t1 ++ col.col_term t2 ++ col.col_term t3
  | Local(decl, t2) -> col.col_term t2 ++ col.col_decl decl
  | BinOp(_, t1, t2) -> col.col_term t1 ++ col.col_term t2
  | Not t1 -> col.col_term t1
  | Event _ -> col.col_empty
  | Record fields -> col_list col (snd |- col.col_term) fields
  | Field(t1,_) -> col.col_term t1
  | SetField(t1,_,t2) -> col.col_term t1 ++ col.col_term t2
  | Nil -> col.col_empty
  | Cons(t1,t2) -> col.col_term t1 ++ col.col_term t2
  | Constr(_,ts) -> col_list col col.col_term ts
  | Match(t1,pats) ->
      let aux acc (pat,t1) = acc ++ col.col_pat pat ++ col.col_term t1 in
      List.fold_left aux (col.col_term t1) pats
  | Raise t -> col.col_term t
  | TryWith(t1,t2) -> col.col_term t1 ++ col.col_term t2
  | Tuple ts -> col_list col col.col_term ts
  | Proj(_,t) -> col.col_term t
  | Bottom -> col.col_empty
  | Label(info, t) -> col.col_info info ++ col.col_term t
  | Ref t -> col.col_term t
  | Deref t -> col.col_term t
  | SetRef(t1,t2) -> col.col_term t1 ++ col.col_term t2
  | TNone -> col.col_empty
  | TSome t -> col.col_term t
  | Module decls -> col_list col col.col_decl decls
  | MemSet(t1, t2) -> col.col_term t1 ++ col.col_term t2
  | AddSet(t1, t2) -> col.col_term t1 ++ col.col_term t2
  | Subset(t1, t2) -> col.col_term t1 ++ col.col_term t2

let col_term col t =
  let (@@) = col.col_app in
  col.col_desc t.desc @@ col.col_typ t.typ @@ col.col_attr t.attr


let make_col empty app =
  let f _ = empty in
  let col =
    {col_term = f;
     col_term_rec = f;
     col_desc = f;
     col_desc_rec = f;
     col_typ = f;
     col_typ_rec = f;
     col_var = f;
     col_var_rec = f;
     col_pat = f;
     col_pat_rec = f;
     col_info = f;
     col_info_rec = f;
     col_decl = f;
     col_decl_rec = f;
     col_const = f;
     col_const_rec = f;
     col_attr = f;
     col_app = app;
     col_empty = empty}
  in
  col.col_term <- col_term col;
  col.col_term_rec <- col_term col;
  col.col_desc <- col_desc col;
  col.col_desc_rec <- col_desc col;
  col.col_typ <- col_typ col;
  col.col_typ_rec <- col_typ col;
  col.col_var <- col_var col;
  col.col_var_rec <- col_var col;
  col.col_pat <- col_pat col;
  col.col_pat_rec <- col_pat col;
  col.col_info <- col_info col;
  col.col_info_rec <- col_info col;
  col.col_decl <- col_decl col;
  col.col_decl_rec <- col_decl col;
  col.col_const <- col_const col;
  col.col_const_rec <- col_const col;
  col






type ('a,'b) col2 =
  {mutable col2_term: 'b -> term -> 'a;
   mutable col2_term_rec: 'b -> term -> 'a;
   mutable col2_desc: 'b -> desc -> 'a;
   mutable col2_desc_rec: 'b -> desc -> 'a;
   mutable col2_typ: 'b -> typ -> 'a;
   mutable col2_typ_rec: 'b -> typ -> 'a;
   mutable col2_var: 'b -> id -> 'a;
   mutable col2_var_rec: 'b -> id -> 'a;
   mutable col2_pat: 'b -> pattern -> 'a;
   mutable col2_pat_rec: 'b -> pattern -> 'a;
   mutable col2_info: 'b -> info -> 'a;
   mutable col2_info_rec: 'b -> info -> 'a;
   mutable col2_decl: 'b -> declaration -> 'a;
   mutable col2_decl_rec: 'b -> declaration -> 'a;
   mutable col2_const: 'b -> const -> 'a;
   mutable col2_const_rec: 'b -> const -> 'a;
   mutable col2_attr: 'b -> attr list -> 'a;
   mutable col2_app: 'a -> 'a -> 'a;
   mutable col2_empty: 'a}

let col2_list col ?(init=col.col2_empty) f xs =
  List.fold_left (fun acc typ -> col.col2_app acc @@ f typ) init xs

let col2_typ col env typ =
  let (++) = col.col2_app in
  match typ with
  | TBase _ -> col.col2_empty
  | TVar({contents=None},_) -> col.col2_empty
  | TVar({contents=Some typ},_) -> col.col2_typ env typ
  | TFun(x,typ) -> col.col2_var env x ++ col.col2_typ env typ
  | TFuns(xs,typ) -> col2_list col (col.col2_var env) ~init:(col.col2_typ env typ) xs
  | TApp(_,typs) -> col2_list col (col.col2_typ env) typs
  | TTuple xs -> col2_list col (col.col2_var env) xs
  | TData _ -> col.col2_empty
  | TAttr(attr, typ) ->
      let aux acc a =
        match a with
        | TAPred(x,ps) ->
            let init = col.col2_var env x ++ acc in
            col2_list col (col.col2_term env) ~init ps
        | TARefPred(x,p) ->
            col.col2_var env x ++ col.col2_term env p ++ acc
        | TAPureFun -> acc
        | TAEffect _ -> acc
        | TAPredShare _ -> acc
        | TAId _ -> acc
        | TARaise ty -> col.col2_typ env ty ++ acc
      in
      List.fold_left aux (col.col2_typ env typ) attr
  | TVariant(_,labels) -> List.fold_left (fun init (_,typs) -> col2_list col (col.col2_typ env) ~init typs) col.col2_empty labels
  | TRecord fields -> col2_list col (snd |- snd |- col.col2_typ env) fields
  | TModule {sig_types; sig_values} ->
      col2_list col (snd |- col.col2_typ env) sig_types ++ col2_list col (col.col2_var env) sig_values

let col2_var col env x = col.col2_typ env (Id.typ x)

let col2_pat col env p =
  let (++) = col.col2_app in
  let r1 = col.col2_typ env p.pat_typ in
  let r2 =
    match p.pat_desc with
    | PAny -> col.col2_empty
    | PNondet -> col.col2_empty
    | PVar x -> col.col2_var env x
    | PAlias(p,x) -> col.col2_pat env p ++ col.col2_var env x
    | PConst t -> col.col2_term env t
    | PConstr(_,ps) -> List.fold_left (fun acc p -> acc ++ col.col2_pat env p) col.col2_empty ps
    | PNil -> col.col2_empty
    | PCons(p1,p2) -> col.col2_pat env p1 ++ col.col2_pat env p2
    | PTuple ps -> List.fold_left (fun acc p -> acc ++ col.col2_pat env p) col.col2_empty ps
    | PRecord pats -> List.fold_left (fun acc (_,p) -> acc ++ col.col2_pat env p) col.col2_empty pats
    | POr(p1,p2) -> col.col2_pat env p1 ++ col.col2_pat env p2
    | PNone -> col.col2_empty
    | PSome p -> col.col2_pat env p
    | PWhen(p,cond) -> col.col2_pat env p ++ col.col2_term env cond
  in
  col.col2_app r1 r2

let col2_info col env = function
  | InfoInt _ -> col.col2_empty
  | InfoString _ -> col.col2_empty
  | InfoId x -> col.col2_var env x
  | InfoTerm t -> col.col2_term env t
  | InfoIdTerm(x, t) -> col.col2_app (col.col2_var env x) (col.col2_term env t)

let col2_const col env c =
  match c with
  | Rand(typ,_) -> col.col2_typ env typ
  | _ -> col.col2_empty

let col2_decl col env decl =
  match decl with
  | Decl_let defs ->
      let aux acc (x,t) =
        col.col2_app acc @@
        col.col2_app (col.col2_var env x) (col.col2_term env t)
      in
      List.fold_left aux col.col2_empty defs
  | Decl_type decls -> col2_list col (snd |- col.col2_typ env) decls
  | Open m -> col.col2_var env m

let col2_desc col env desc =
  let (++) = col.col2_app in
  match desc with
  | End_of_definitions -> col.col2_empty
  | Const c -> col.col2_const env c
  | Var y -> col.col2_var env y
  | Fun(y, t) -> col.col2_var env y ++ col.col2_term env t
  | App(t1, ts) -> List.fold_left (fun acc t -> acc ++ col.col2_term env t) (col.col2_term env t1) ts
  | If(t1, t2, t3) -> col.col2_term env t1 ++ col.col2_term env t2 ++ col.col2_term env t3
  | Local(decl, t2) -> col.col2_term env t2 ++ col.col2_decl env decl
  | BinOp(_, t1, t2) -> col.col2_term env t1 ++ col.col2_term env t2
  | Not t1 -> col.col2_term env t1
  | Event _ -> col.col2_empty
  | Record fields -> List.fold_left (fun acc (_,t1) -> acc ++ col.col2_term env t1) col.col2_empty fields
  | Field(t1,_) -> col.col2_term env t1
  | SetField(t1,_,t2) -> col.col2_term env t1 ++ col.col2_term env t2
  | Nil -> col.col2_empty
  | Cons(t1,t2) -> col.col2_term env t1 ++ col.col2_term env t2
  | Constr(_,ts) -> List.fold_left (fun acc t -> acc ++ col.col2_term env t) col.col2_empty ts
  | Match(t1,pats) ->
      let aux acc (pat,t1) =
        acc ++
        col.col2_pat env pat ++
        col.col2_term env t1
      in
      List.fold_left aux (col.col2_term env t1) pats
  | Raise t -> col.col2_term env t
  | TryWith(t1,t2) -> col.col2_term env t1 ++ col.col2_term env t2
  | Tuple ts -> List.fold_left (fun acc t -> acc ++ col.col2_term env t) col.col2_empty ts
  | Proj(_,t) -> col.col2_term env t
  | Bottom -> col.col2_empty
  | Label(info, t) -> col.col2_info env info ++ col.col2_term env t
  | Ref t -> col.col2_term env t
  | Deref t -> col.col2_term env t
  | SetRef(t1,t2) -> col.col2_term env t1 ++ col.col2_term env t2
  | TNone -> col.col2_empty
  | TSome t -> col.col2_term env t
  | Module decls -> List.fold_left (fun acc decl -> acc ++ col.col2_decl env decl) col.col2_empty decls
  | MemSet(t1, t2) -> col.col2_term env t1 ++ col.col2_term env t2
  | AddSet(t1, t2) -> col.col2_term env t1 ++ col.col2_term env t2
  | Subset(t1, t2) -> col.col2_term env t1 ++ col.col2_term env t2

let col2_term col env t = col.col2_app (col.col2_desc env t.desc) (col.col2_typ env t.typ)


let make_col2  : 'a -> ('a -> 'a -> 'a) -> ('a,'b) col2 = fun (empty:'a) app ->
  let f _ _ = empty in
  let col =
    {col2_term = f;
     col2_term_rec = f;
     col2_desc = f;
     col2_desc_rec = f;
     col2_typ = f;
     col2_typ_rec = f;
     col2_var = f;
     col2_var_rec = f;
     col2_pat = f;
     col2_pat_rec = f;
     col2_info = f;
     col2_info_rec = f;
     col2_const = f;
     col2_const_rec = f;
     col2_decl = f;
     col2_decl_rec = f;
     col2_attr = f;
     col2_app = app;
     col2_empty = empty}
  in
  col.col2_term <- col2_term col;
  col.col2_term_rec <- col2_term col;
  col.col2_desc <- col2_desc col;
  col.col2_desc_rec <- col2_desc col;
  col.col2_typ <- col2_typ col;
  col.col2_typ_rec <- col2_typ col;
  col.col2_var <- col2_var col;
  col.col2_var_rec <- col2_var col;
  col.col2_pat <- col2_pat col;
  col.col2_pat_rec <- col2_pat col;
  col.col2_info <- col2_info col;
  col.col2_info_rec <- col2_info col;
  col.col2_decl <- col2_decl col;
  col.col2_decl_rec <- col2_decl col;
  col.col2_const <- col2_const col;
  col.col2_const_rec <- col2_const col;
  col




type ('a,'b) tr_col2 =
  {mutable tr_col2_term:      'b -> term    -> 'a * term;
   mutable tr_col2_term_rec:  'b -> term    -> 'a * term;
   mutable tr_col2_desc:      'b -> desc          -> 'a * desc;
   mutable tr_col2_desc_rec:  'b -> desc          -> 'a * desc;
   mutable tr_col2_typ:       'b -> typ           -> 'a * typ;
   mutable tr_col2_typ_rec:   'b -> typ           -> 'a * typ;
   mutable tr_col2_var:       'b -> id            -> 'a * id;
   mutable tr_col2_var_rec:   'b -> id            -> 'a * id;
   mutable tr_col2_pat:       'b -> pattern -> 'a * pattern;
   mutable tr_col2_pat_rec:   'b -> pattern -> 'a * pattern;
   mutable tr_col2_info:      'b -> info          -> 'a * info;
   mutable tr_col2_info_rec:  'b -> info          -> 'a * info;
   mutable tr_col2_decl:      'b -> declaration   -> 'a * declaration;
   mutable tr_col2_decl_rec:  'b -> declaration   -> 'a * declaration;
   mutable tr_col2_const:     'b -> const         -> 'a * const;
   mutable tr_col2_const_rec: 'b -> const         -> 'a * const;
   mutable tr_col2_attr:      'b -> attr list     -> 'a * attr list;
   mutable tr_col2_app: 'a -> 'a -> 'a;
   mutable tr_col2_empty: 'a}

let tr_col2_list tc tr_col ?(init=tc.tr_col2_empty) env xs =
  let aux x (acc,xs) =
    let acc',x' = tr_col env x in
    tc.tr_col2_app acc acc', x'::xs
  in
  List.fold_right aux xs (init,[])

let tr_col2_typ tc env ty =
  let (++) = tc.tr_col2_app in
  match ty with
  | TBase b -> tc.tr_col2_empty, TBase b
  | TVar({contents=None} as x,id) -> tc.tr_col2_empty, TVar(x,id)
  | TVar({contents=Some typ},_) -> tc.tr_col2_typ env typ
  | TFun(x,typ) ->
      let acc1,x' = tc.tr_col2_var env x in
      let acc2,typ' = tc.tr_col2_typ env typ in
      acc1 ++ acc2, TFun(x', typ')
  | TFuns(xs,typ) ->
      let acc1,xs' = tr_col2_list tc tc.tr_col2_var env xs in
      let acc2,typ' = tc.tr_col2_typ env typ in
      acc1 ++ acc2, TFuns(xs', typ')
  | TApp(c, typs) ->
      let acc,typs' = tr_col2_list tc tc.tr_col2_typ env typs in
      acc, TApp(c, typs')
  | TTuple xs ->
      let acc,xs' = tr_col2_list tc tc.tr_col2_var env xs in
      acc, TTuple xs'
  | TData s -> tc.tr_col2_empty, TData s
  | TAttr(attr, typ) ->
      let aux env a =
        match a with
        | TAPred(x,ps) ->
            let acc,x' = tc.tr_col2_var env x in
            let acc',ps' = tr_col2_list tc tc.tr_col2_term ~init:acc env ps in
            acc', TAPred(x',ps')
        | TARefPred(x,p) ->
            let acc,x' = tc.tr_col2_var env x in
            let acc',p' = tc.tr_col2_term env p in
            acc ++ acc', TARefPred(x',p')
        | TAPureFun -> tc.tr_col2_empty, TAPureFun
        | TAEffect e -> tc.tr_col2_empty, TAEffect e
        | TAPredShare x -> tc.tr_col2_empty, TAPredShare x
        | TAId(s,n) -> tc.tr_col2_empty, TAId(s,n)
        | TARaise ty ->
            let acc,ty' = tc.tr_col2_typ env ty in
            acc, TARaise ty'
      in
      let acc,typ' = tc.tr_col2_typ env typ in
      let acc',attr' = tr_col2_list tc aux ~init:acc env attr in
      acc', TAttr(attr', typ')
  | TVariant(poly,labels) ->
      let acc,labels' =
        let aux (s,typs) (acc,labels') =
          let acc',typs' = tr_col2_list tc tc.tr_col2_typ ~init:acc env typs in
          acc', (s,typs')::labels'
        in
        List.fold_right aux labels (tc.tr_col2_empty,[])
      in
      acc, TVariant(poly,labels')
  | TRecord fields ->
      let acc,fields' =
        let aux env' (s,(f,typ)) =
          let acc,typ' = tc.tr_col2_typ env' typ in
          acc, (s,(f,typ'))
        in
        tr_col2_list tc aux env fields
      in
      acc, TRecord fields'
  | TModule {sig_types; sig_values} ->
      let acc,sig_types =
        let aux env' (s,typ) =
          let acc,typ' = tc.tr_col2_typ env' typ in
          acc, (s,typ')
        in
        tr_col2_list tc aux env sig_types
      in
      let acc,sig_values = tr_col2_list tc tc.tr_col2_var ~init:acc env sig_values in
      acc, TModule {sig_types; sig_values}

let tr_col2_var tc env x =
  let acc,typ' = tc.tr_col2_typ env (Id.typ x) in
  acc, Id.set_typ x typ'

let tr_col2_pat tc env p =
  let (++) = tc.tr_col2_app in
  let acc1,typ = tc.tr_col2_typ env p.pat_typ in
  let acc2,desc =
    match p.pat_desc with
    | PAny -> tc.tr_col2_empty, PAny
    | PNondet -> tc.tr_col2_empty, PNondet
    | PVar x ->
        let acc,x' = tc.tr_col2_var env x in
        acc, PVar x'
    | PAlias(p,x) ->
        let acc1,p' = tc.tr_col2_pat env p in
        let acc2,x' = tc.tr_col2_var env x in
        acc1 ++ acc2, PAlias(p',x')
    | PConst t ->
        let acc,t' = tc.tr_col2_term env t in
        acc, PConst t'
    | PConstr(s,ps) ->
        let acc,ps' = tr_col2_list tc tc.tr_col2_pat env ps in
        acc, PConstr(s,ps')
    | PNil -> tc.tr_col2_empty, PNil
    | PCons(p1,p2) ->
        let acc1,p1' = tc.tr_col2_pat env p1 in
        let acc2,p2' = tc.tr_col2_pat env p2 in
        acc1 ++ acc2, PCons(p1', p2')
    | PTuple ps ->
        let acc,ps' = tr_col2_list tc tc.tr_col2_pat env ps in
        acc, PTuple ps'
    | PRecord pats ->
        let aux env (s,p) =
          let acc',p' = tc.tr_col2_pat env p in
          acc', (s,p')
        in
        let acc,pats' = tr_col2_list tc aux env pats in
        acc, PRecord pats'
    | POr(p1,p2) ->
        let acc1,p1' = tc.tr_col2_pat env p1 in
        let acc2,p2' = tc.tr_col2_pat env p2 in
        acc1 ++ acc2, POr(p1', p2')
    | PNone -> tc.tr_col2_empty, PNone
    | PSome p ->
        let acc,p' = tc.tr_col2_pat env p in
        acc, PSome p'
    | PWhen(p,cond) ->
        let acc1,p' = tc.tr_col2_pat env p in
        let acc2,cond' = tc.tr_col2_term env cond in
        acc1 ++ acc2, PWhen(p', cond')
  in
  acc1 ++ acc2, {pat_desc=desc; pat_typ=typ}

let tr_col2_info tc env = function
  | InfoInt n -> tc.tr_col2_empty, InfoInt n
  | InfoString s -> tc.tr_col2_empty, InfoString s
  | InfoId x ->
      let acc,x' = tc.tr_col2_var env x in
      acc, InfoId x'
  | InfoTerm t ->
      let acc,t' = tc.tr_col2_term env t in
      acc, InfoTerm t'
  | InfoIdTerm(x,t) ->
      let acc1,x' = tc.tr_col2_var env x in
      let acc2,t' = tc.tr_col2_term env t in
      tc.tr_col2_app acc1 acc2, InfoIdTerm(x',t')

let tr_col2_const tc env c =
  match c with
  | Rand(typ,b) ->
      let acc,typ' = tc.tr_col2_typ env typ in
      acc, Rand(typ',b)
  | _ -> tc.tr_col2_empty, c

let tr_col2_decl tc env decl =
  match decl with
  | Decl_let defs ->
      let aux env (x,t) =
        let acc1,x' = tc.tr_col2_var env x in
        let acc2,t' = tc.tr_col2_term env t in
        tc.tr_col2_app acc1 acc2, (x',t')
      in
      let acc,defs' = tr_col2_list tc aux env defs in
      acc, Decl_let defs'
  | Decl_type decls ->
      let aux env (name,ty) =
        let acc, ty' = tc.tr_col2_typ env ty in
        acc, (name, ty')
      in
      let acc,decls' = tr_col2_list tc aux env decls in
      acc, Decl_type decls'
  | Open m ->
      let acc, m' = tc.tr_col2_var env m in
      acc, Open m'

let tr_col2_desc tc env desc =
  let (++) = tc.tr_col2_app in
  match desc with
  | End_of_definitions -> tc.tr_col2_empty, End_of_definitions
  | Const c ->
      let acc,c' = tc.tr_col2_const env c in
      acc, Const c'
  | Var y ->
      let acc,y' = tc.tr_col2_var env y in
      acc, Var y'
  | Fun(y, t) ->
      let acc1,y' = tc.tr_col2_var env y in
      let acc2,t' = tc.tr_col2_term env t in
      acc1 ++ acc2, Fun(y',t')
  | App(t1, ts) ->
      let acc,t1' = tc.tr_col2_term env t1 in
      let acc',ts' = tr_col2_list tc tc.tr_col2_term ~init:acc env ts in
      acc', App(t1', ts')
  | If(t1, t2, t3) ->
      let acc1,t1' = tc.tr_col2_term env t1 in
      let acc2,t2' = tc.tr_col2_term env t2 in
      let acc3,t3' = tc.tr_col2_term env t3 in
      tc.tr_col2_app acc1 @@ tc.tr_col2_app acc2 acc3, If(t1',t2',t3')
  | Local(decl, t2) ->
      let acc1,decl' = tc.tr_col2_decl env decl in
      let acc2,t2' = tc.tr_col2_term env t2 in
      acc1 ++ acc2, Local(decl',t2')
  | BinOp(op, t1, t2) ->
      let acc1,t1' = tc.tr_col2_term env t1 in
      let acc2,t2' = tc.tr_col2_term env t2 in
      acc1 ++ acc2, BinOp(op,t1',t2')
  | Not t1 ->
      let acc,t1' = tc.tr_col2_term env t1 in
      acc, Not t1'
  | Event(s,b) -> tc.tr_col2_empty, Event(s,b)
  | Record fields ->
      let aux env (s,t1) =
        let acc,t1' = tc.tr_col2_term env t1 in
        acc, (s,t1')
      in
      let acc,fields' = tr_col2_list tc aux env fields in
      acc, Record fields'
  | Field(t1,s) ->
      let acc,t1' = tc.tr_col2_term env t1 in
      acc, Field(t1',s)
  | SetField(t1,s,t2) ->
      let acc1,t1' = tc.tr_col2_term env t1 in
      let acc2,t2' = tc.tr_col2_term env t2 in
      acc1 ++ acc2, SetField(t1',s,t2')
  | Nil -> tc.tr_col2_empty, Nil
  | Cons(t1,t2) ->
      let acc1,t1' = tc.tr_col2_term env t1 in
      let acc2,t2' = tc.tr_col2_term env t2 in
      acc1 ++ acc2, Cons(t1',t2')
  | Constr(s,ts) ->
      let acc,ts' = tr_col2_list tc tc.tr_col2_term env ts in
      acc, Constr(s,ts')
  | Match(t1,pats) ->
      let aux env (pat,t1) =
        let acc1,pat' = tc.tr_col2_pat env pat in
        let acc2,t1' = tc.tr_col2_term env t1 in
        acc1 ++ acc2, (pat',t1')
      in
      let acc,t1' = tc.tr_col2_term env t1 in
      let acc',pats' = tr_col2_list tc aux ~init:acc env pats in
      acc', Match(t1',pats')
  | Raise t ->
      let acc,t' = tc.tr_col2_term env t in
      acc, Raise t'
  | TryWith(t1,t2) ->
      let acc1,t1' = tc.tr_col2_term env t1 in
      let acc2,t2' = tc.tr_col2_term env t2 in
      acc1 ++ acc2, TryWith(t1',t2')
  | Tuple ts ->
      let acc,ts' = tr_col2_list tc tc.tr_col2_term env ts in
      acc, Tuple ts'
  | Proj(i,t) ->
      let acc,t' = tc.tr_col2_term env t in
      acc, Proj(i,t')
  | Bottom -> tc.tr_col2_empty, Bottom
  | Label(info, t) ->
      let acc1,t' = tc.tr_col2_term env t in
      let acc2,info' = tc.tr_col2_info env info in
      acc1 ++ acc2, Label(info',t')
  | Ref t ->
      let acc,t' = tc.tr_col2_term env t in
      acc, Ref t'
  | Deref t ->
      let acc,t' = tc.tr_col2_term env t in
      acc, Deref t'
  | SetRef(t1,t2) ->
      let acc1,t1' = tc.tr_col2_term env t1 in
      let acc2,t2' = tc.tr_col2_term env t2 in
      acc1 ++ acc2, SetRef(t1',t2')
  | TNone -> tc.tr_col2_empty, TNone
  | TSome t ->
      let acc,t' = tc.tr_col2_term env t in
      acc, TSome t'
  | Module decls ->
      let acc,decls' = tr_col2_list tc tc.tr_col2_decl env decls in
      acc, Module decls'
  | MemSet(t1, t2) ->
      let acc1,t1' = tc.tr_col2_term env t1 in
      let acc2,t2' = tc.tr_col2_term env t2 in
      acc1 ++ acc2, MemSet(t1',t2')
  | AddSet(t1, t2) ->
      let acc1,t1' = tc.tr_col2_term env t1 in
      let acc2,t2' = tc.tr_col2_term env t2 in
      acc1 ++ acc2, AddSet(t1',t2')
  | Subset(t1, t2) ->
      let acc1,t1' = tc.tr_col2_term env t1 in
      let acc2,t2' = tc.tr_col2_term env t2 in
      acc1 ++ acc2, Subset(t1',t2')


let tr_col2_term tc env t =
  let (++) = tc.tr_col2_app in
  let acc1,desc = tc.tr_col2_desc env t.desc in
  let acc2,typ = tc.tr_col2_typ env t.typ in
  let acc3,attr = tc.tr_col2_attr env t.attr in
  acc1++acc2++acc3, {desc; typ; attr}


let make_tr_col2 empty app =
  let f _ x = empty, x in
  let tc =
    {tr_col2_term = f;
     tr_col2_term_rec = f;
     tr_col2_desc = f;
     tr_col2_desc_rec = f;
     tr_col2_typ = f;
     tr_col2_typ_rec = f;
     tr_col2_var = f;
     tr_col2_var_rec = f;
     tr_col2_pat = f;
     tr_col2_pat_rec = f;
     tr_col2_info = f;
     tr_col2_info_rec = f;
     tr_col2_decl = f;
     tr_col2_decl_rec = f;
     tr_col2_const = f;
     tr_col2_const_rec = f;
     tr_col2_attr = f;
     tr_col2_app = app;
     tr_col2_empty = empty}
  in
  tc.tr_col2_term <- tr_col2_term tc;
  tc.tr_col2_term_rec <- tr_col2_term tc;
  tc.tr_col2_desc <- tr_col2_desc tc;
  tc.tr_col2_desc_rec <- tr_col2_desc tc;
  tc.tr_col2_typ <- tr_col2_typ tc;
  tc.tr_col2_typ_rec <- tr_col2_typ tc;
  tc.tr_col2_var <- tr_col2_var tc;
  tc.tr_col2_var_rec <- tr_col2_var tc;
  tc.tr_col2_pat <- tr_col2_pat tc;
  tc.tr_col2_pat_rec <- tr_col2_pat tc;
  tc.tr_col2_info <- tr_col2_info tc;
  tc.tr_col2_info_rec <- tr_col2_info tc;
  tc.tr_col2_decl <- tr_col2_decl tc;
  tc.tr_col2_decl_rec <- tr_col2_decl tc;
  tc.tr_col2_const <- tr_col2_const tc;
  tc.tr_col2_const_rec <- tr_col2_const tc;
  tc







type 'a fold_tr =
  {mutable fld_term:      'a -> term        -> 'a * term;
   mutable fld_term_rec:  'a -> term        -> 'a * term;
   mutable fld_desc:      'a -> desc        -> 'a * desc;
   mutable fld_desc_rec:  'a -> desc        -> 'a * desc;
   mutable fld_typ:       'a -> typ         -> 'a * typ;
   mutable fld_typ_rec:   'a -> typ         -> 'a * typ;
   mutable fld_var:       'a -> id          -> 'a * id;
   mutable fld_var_rec:   'a -> id          -> 'a * id;
   mutable fld_pat:       'a -> pattern     -> 'a * pattern;
   mutable fld_pat_rec:   'a -> pattern     -> 'a * pattern;
   mutable fld_info:      'a -> info        -> 'a * info;
   mutable fld_info_rec:  'a -> info        -> 'a * info;
   mutable fld_decl:      'a -> declaration -> 'a * declaration;
   mutable fld_decl_rec:  'a -> declaration -> 'a * declaration;
   mutable fld_const:     'a -> const       -> 'a * const;
   mutable fld_const_rec: 'a -> const       -> 'a * const;
   mutable fld_attr:      'a -> attr list   -> 'a * attr list}

let fold_tr_list_right tr_col env xs =
  let aux x (env,xs) =
    let env',x' = tr_col env x in
    env', x'::xs
  in
  List.fold_right aux xs (env,[])
let fold_tr_list = fold_tr_list_right

let fold_tr_list_left tr_col env xs =
  let aux (env,xs_rev) x =
    let env',x' = tr_col env x in
    env', x'::xs_rev
  in
  let env',xs_rev = List.fold_left aux (env,[]) xs in
  env', List.rev xs_rev


let fold_tr_typ fld env ty =
  match ty with
  | TBase b -> env, TBase b
  | TVar({contents=None} as x,id) -> env, TVar(x,id)
  | TVar({contents=Some typ},_) -> fld.fld_typ env typ
  | TFun(x,typ) ->
      let env',x' = fld.fld_var env x in
      let env'',typ' = fld.fld_typ env' typ in
      env'', TFun(x', typ')
  | TApp(c, typs) ->
      let env',typs' = fold_tr_list fld.fld_typ env typs in
      env', TApp(c, typs')
  | TTuple xs ->
      let env',xs' = fold_tr_list fld.fld_var env xs in
      env', TTuple xs'
  | TData s -> env, TData s
  | TAttr(attr, typ) ->
      let aux env a =
        match a with
        | TAPred(x,ps) ->
            let env',x' = fld.fld_var env x in
            let env'',ps' = fold_tr_list fld.fld_term env' ps in
            env'', TAPred(x',ps')
        | TARefPred(x,p) ->
            let env',x' = fld.fld_var env x in
            let env'',p' = fld.fld_term env' p in
            env'', TARefPred(x',p')
        | TAPureFun -> env, TAPureFun
        | TAEffect e -> env, TAEffect e
        | TAPredShare x -> env, TAPredShare x
        | TAId(s,x) -> env, TAId(s,x)
        | TARaise ty ->
            let env,ty' = fld.fld_typ env ty in
            env, TARaise ty'
      in
      let env',attr' = fold_tr_list aux env attr in
      let env'',typ' = fld.fld_typ env' typ in
      env'', TAttr(attr', typ')
  | TVariant(poly,labels) ->
      let env,labels' =
        let aux (s,typs) (env,labels') =
          let env',typs' = fold_tr_list fld.fld_typ env typs in
          env', (s,typs')::labels'
        in
        List.fold_right aux labels (env,[])
      in
      env, TVariant(poly,labels')
  | TRecord fields ->
      let env,fields' =
        let aux env' (s,(f,typ)) =
          let env,typ' = fld.fld_typ env' typ in
          env, (s,(f,typ'))
        in
        fold_tr_list aux env fields
      in
      env, TRecord fields'
  | TModule {sig_types; sig_values} ->
      let env,sig_types =
        let aux env (s,typ) =
          let env,typ' = fld.fld_typ env typ in
          env, (s,typ')
        in
        fold_tr_list aux env sig_types
      in
      let env,sig_values = fold_tr_list fld.fld_var env sig_values in
      env, TModule {sig_types; sig_values}
  | TFuns _ -> unsupported "fld"

let fold_tr_var fld env x =
  let env',typ' = fld.fld_typ env (Id.typ x) in
  env', Id.set_typ x typ'

let fold_tr_pat fld env p =
  let env',typ = fld.fld_typ env p.pat_typ in
  let env'',desc =
    match p.pat_desc with
    | PAny -> env', PAny
    | PNondet -> env', PNondet
    | PVar x ->
        let env'',x' = fld.fld_var env' x in
        env'', PVar x'
    | PAlias(p,x) ->
        let env'',p' = fld.fld_pat env' p in
        let env''',x' = fld.fld_var env'' x in
        env''', PAlias(p',x')
    | PConst t ->
        let env'',t' = fld.fld_term env' t in
        env'', PConst t'
    | PConstr(s,ps) ->
        let env'',ps' = fold_tr_list fld.fld_pat env ps in
        env'', PConstr(s,ps')
    | PNil -> env', PNil
    | PCons(p1,p2) ->
        let env'',p1' = fld.fld_pat env' p1 in
        let env''',p2' = fld.fld_pat env'' p2 in
        env''', PCons(p1', p2')
    | PTuple ps ->
        let env'',ps' = fold_tr_list fld.fld_pat env' ps in
        env'', PTuple ps'
    | PRecord pats ->
        let aux env (s,p) =
          let env',p' = fld.fld_pat env p in
          env', (s,p')
        in
        let env'',pats' = fold_tr_list aux env' pats in
        env'', PRecord pats'
    | POr(p1,p2) ->
        let env'',p1' = fld.fld_pat env' p1 in
        let env''',p2' = fld.fld_pat env'' p2 in
        env''', POr(p1', p2')
    | PNone -> env', PNone
    | PSome p ->
        let env'',p' = fld.fld_pat env' p in
        env'', PSome p'
    | PWhen(p,cond) ->
        let env'',p' = fld.fld_pat env' p in
        let env''',cond' = fld.fld_term env'' cond in
        env''', PWhen(p', cond')
  in
  env'', {pat_desc=desc; pat_typ=typ}

let fold_tr_info fld env = function
  | InfoInt n -> env, InfoInt n
  | InfoString s -> env, InfoString s
  | InfoId x ->
      let env',x' = fld.fld_var env x in
      env', InfoId x'
  | InfoTerm t ->
      let env',t' = fld.fld_term env t in
      env', InfoTerm t'
  | InfoIdTerm(x,t) ->
      let env',x' = fld.fld_var env x in
      let env'',t' = fld.fld_term env' t in
      env'', InfoIdTerm(x',t')

let fold_tr_const fld env c =
  match c with
  | Rand(typ,b) ->
      let env',typ' = fld.fld_typ env typ in
      env', Rand(typ',b)
  | _ -> env, c

let fold_tr_decl fld env decl =
  match decl with
  | Decl_let defs ->
      let aux env (x,t) =
        let env,x' = fld.fld_var env x in
        let env,t' = fld.fld_term env t in
        env, (x',t')
      in
      let env,defs' = fold_tr_list_left aux env defs in
      env, Decl_let defs'
  | Decl_type decls ->
      let aux env (name,ty) =
        let env',ty' = fld.fld_typ env ty in
        env', (name, ty')
      in
      let env',decls' = fold_tr_list aux env decls in
      env', Decl_type decls'
  | Open m ->
      let env',m' = fld.fld_var env m in
      env', Open m'

let fold_tr_desc fld env = function
  | End_of_definitions -> env, End_of_definitions
  | Const c ->
      let env',c' = fld.fld_const env c in
      env', Const c'
  | Var y ->
      let env',y' = fld.fld_var env y in
      env', Var y'
  | Fun(y, t) ->
      let env',y' = fld.fld_var env y in
      let env'',t' = fld.fld_term env' t in
      env'', Fun(y',t')
  | App(t1, ts) ->
      if Flag.EvalStrategy.app_left_to_right then
        let env,t1' = fld.fld_term env t1 in
        let env,ts' = fold_tr_list_left fld.fld_term env ts in
        env, App(t1', ts')
      else
        let env,ts' = fold_tr_list_right fld.fld_term env ts in
        let env,t1' = fld.fld_term env t1 in
        env, App(t1', ts')
  | If(t1, t2, t3) ->
      let env',t1' = fld.fld_term env t1 in
      let env'',t2' = fld.fld_term env' t2 in
      let env''',t3' = fld.fld_term env'' t3 in
      env''', If(t1',t2',t3')
  | Local(decl, t2) ->
      let env',decl' = fld.fld_decl env decl in
      let env'',t2' = fld.fld_term env' t2 in
      env'', Local(decl',t2')
  | BinOp(op, t1, t2) ->
      if Flag.EvalStrategy.binop_left_to_right || List.mem op [And;Or] then
        let env,t1' = fld.fld_term env t1 in
        let env,t2' = fld.fld_term env t2 in
        env, BinOp(op,t1',t2')
      else
        let env,t2' = fld.fld_term env t2 in
        let env,t1' = fld.fld_term env t1 in
        env, BinOp(op,t1',t2')
  | Not t1 ->
      let env',t1' = fld.fld_term env t1 in
      env', Not t1'
  | Event(s,b) -> env, Event(s,b)
  | Record fields ->
      let aux env (s,t1) =
        let env',t1' = fld.fld_term env t1 in
        env', (s,t1')
      in
      let env',fields' =
        let fold = if Flag.EvalStrategy.record_left_to_right then fold_tr_list_left else fold_tr_list_right in
        fold aux env fields
      in
      env', Record fields'
  | Field(t1,s) ->
      let env',t1' = fld.fld_term env t1 in
      env', Field(t1',s)
  | SetField(t1,s,t2) ->
      if Flag.EvalStrategy.setfield_left_to_right then
        let env,t1' = fld.fld_term env t1 in
        let env,t2' = fld.fld_term env t2 in
        env, SetField(t1',s,t2')
      else
        let env,t2' = fld.fld_term env t2 in
        let env,t1' = fld.fld_term env t1 in
        env, SetField(t1',s,t2')
  | Nil -> env, Nil
  | Cons(t1,t2) ->
      if Flag.EvalStrategy.constr_left_to_right then
        let env,t1' = fld.fld_term env t1 in
        let env,t2' = fld.fld_term env t2 in
        env, Cons(t1',t2')
      else
        let env,t2' = fld.fld_term env t2 in
        let env,t1' = fld.fld_term env t1 in
        env, Cons(t1',t2')
  | Constr(s,ts) ->
      let env',ts' =
        let fold = if Flag.EvalStrategy.constr_left_to_right then fold_tr_list_left else fold_tr_list_right in
        fold fld.fld_term env ts in
      env', Constr(s,ts')
  | Match(t1,pats) ->
      let aux env (pat,t1) =
        let env,pat' = fld.fld_pat env pat in
        let env,t1' = fld.fld_term env t1 in
        env, (pat',t1')
      in
      let env,t1' = fld.fld_term env t1 in
      let env,pats' = fold_tr_list_left aux env pats in
      env, Match(t1',pats')
  | Raise t ->
      let env',t' = fld.fld_term env t in
      env', Raise t'
  | TryWith(t1,t2) ->
      let env',t1' = fld.fld_term env t1 in
      let env'',t2' = fld.fld_term env' t2 in
      env'', TryWith(t1',t2')
  | Tuple ts ->
      let env',ts' =
        let fold = if Flag.EvalStrategy.tuple_left_to_right then fold_tr_list_left else fold_tr_list_right in
        fold fld.fld_term env ts
      in
      env', Tuple ts'
  | Proj(i,t) ->
      let env',t' = fld.fld_term env t in
      env', Proj(i,t')
  | Bottom -> env, Bottom
  | Label(info, t) ->
      let env',t' = fld.fld_term env t in
      let env'',info' = fld.fld_info env' info in
      env'', Label(info',t')
  | Ref t ->
      let env',t' = fld.fld_term env t in
      env', Ref t'
  | Deref t ->
      let env',t' = fld.fld_term env t in
      env', Deref t'
  | SetRef(t1,t2) ->
      if Flag.EvalStrategy.setref_left_to_right then
        let env,t1' = fld.fld_term env t1 in
        let env,t2' = fld.fld_term env t2 in
        env, SetRef(t1',t2')
      else
        let env,t2' = fld.fld_term env t2 in
        let env,t1' = fld.fld_term env t1 in
        env, SetRef(t1',t2')
  | TNone -> env, TNone
  | TSome t ->
      let env',t' = fld.fld_term env t in
      env', TSome t'
  | Module decls ->
      let env',decls' = fold_tr_list_left fld.fld_decl env decls  in
      env', Module decls'
  | MemSet(t1, t2) ->
        let env,t1' = fld.fld_term env t1 in
        let env,t2' = fld.fld_term env t2 in
        env, MemSet(t1',t2')
  | AddSet(t1, t2) ->
        let env,t1' = fld.fld_term env t1 in
        let env,t2' = fld.fld_term env t2 in
        env, AddSet(t1',t2')
  | Subset(t1, t2) ->
        let env,t1' = fld.fld_term env t1 in
        let env,t2' = fld.fld_term env t2 in
        env, Subset(t1',t2')

let fold_tr_term fld env t =
  let env,desc = fld.fld_desc env t.desc in
  let env,typ = fld.fld_typ env t.typ in
  let env,attr = fld.fld_attr env t.attr in
  env, {desc; typ; attr}


let make_fold_tr () =
  let f env x = env, x in
  let fld =
    {fld_term = f;
     fld_term_rec = f;
     fld_desc = f;
     fld_desc_rec = f;
     fld_typ = f;
     fld_typ_rec = f;
     fld_var = f;
     fld_var_rec = f;
     fld_pat = f;
     fld_pat_rec = f;
     fld_info = f;
     fld_info_rec = f;
     fld_decl = f;
     fld_decl_rec = f;
     fld_const = f;
     fld_const_rec = f;
     fld_attr = f}
  in
  fld.fld_term <- fold_tr_term fld;
  fld.fld_term_rec <- fold_tr_term fld;
  fld.fld_desc <- fold_tr_desc fld;
  fld.fld_desc_rec <- fold_tr_desc fld;
  fld.fld_typ <- fold_tr_typ fld;
  fld.fld_typ_rec <- fold_tr_typ fld;
  fld.fld_var <- fold_tr_var fld;
  fld.fld_var_rec <- fold_tr_var fld;
  fld.fld_pat <- fold_tr_pat fld;
  fld.fld_pat_rec <- fold_tr_pat fld;
  fld.fld_info <- fold_tr_info fld;
  fld.fld_info_rec <- fold_tr_info fld;
  fld.fld_decl <- fold_tr_decl fld;
  fld.fld_decl_rec <- fold_tr_decl fld;
  fld.fld_const <- fold_tr_const fld;
  fld.fld_const_rec <- fold_tr_const fld;
  fld




let get_vars =
  let col = make_col [] (@@@) in
  col.col_var <- List.singleton;
  col.col_term

let get_bv,get_bv_pat =
  let col = make_col [] (@@@) in
  let col_desc desc =
    match desc with
    | Fun(x,t) -> x :: col.col_term t
    | Local(Decl_let bindings,t) ->
        let aux (f,t) = f :: col.col_term t in
        col.col_term t @@@ List.rev_map_flatten aux bindings
    | _ -> col.col_desc_rec desc
  in
  let col_pat p =
    match p.pat_desc with
    | PVar x -> [x]
    | _ -> col.col_pat_rec p
  in
  col.col_desc <- col_desc;
  col.col_pat <- col_pat;
  col.col_typ <- Fun.const [];
  col.col_term, col.col_pat


let get_fv =
  let col = make_col2 [] (@@@) in
  let col_desc bv desc =
    match desc with
    | Var x when Id.mem x bv -> []
    | Var x when Id.is_primitive x -> []
    | Var x -> [x]
    | Local(Decl_let bindings, t2) ->
        let bv' = List.fold_left (fun bv (f,_) -> f::bv) bv bindings in
        let aux fv (_,t) = col.col2_term bv' t @@@ fv in
        let fv_t2 = col.col2_term bv' t2 in
        List.fold_left aux fv_t2 bindings
    | Fun(x,t) -> col.col2_term (x::bv) t
    | Match(t,pats) ->
        let aux acc (pat,t) =
          let bv' = get_bv_pat pat @@@ bv in
          col.col2_term bv' t @@@ acc
        in
        List.fold_left aux (col.col2_term bv t) pats
    | _ -> col.col2_desc_rec bv desc
  in
  col.col2_desc <- col_desc;
  col.col2_typ <- Fun.const2 [];
  fun ?(eq=Id.eq) t ->
    List.unique ~eq @@ col.col2_term [] t


let id_trans = make_trans ()


let occur_typ =
  let col = make_col2 false (||) in
  let occur_typ x typ =
    match typ with
    | TAttr(attr, typ) ->
        let aux a =
          match a with
          | TAPred(_,ps) -> List.exists (List.exists (Id.same x) -| get_fv) ps
          | TARefPred(_,p) -> List.exists (Id.same x) @@ get_fv p
          | _ -> false
        in
        List.exists aux attr || col.col2_typ x typ
    | _ -> col.col2_typ_rec x typ
  in
  col.col2_typ <- occur_typ;
  col.col2_typ


let is_non_rec bindings =
  match bindings with
  | [] -> assert false
  | [f, t] -> not @@ Id.mem f @@ get_fv t
  | _ -> false

let is_module t =
  match t.desc, elim_tattr t.typ with
  | Module _, _
  | _, TModule _ -> true
  | _ -> false

let rec is_functor t =
  match t.desc, elim_tattr t.typ with
  | Fun(_,t'), _ -> is_module t' || is_functor t'
  | _, TFun(_, TModule _) -> true
  | _ -> false

let rec decomp_funs t =
  match t.desc with
  | Fun(x,t) ->
      let xs,t' = decomp_funs t in
      x::xs, t'
  | _ -> [], t

let rec decomp_locals t =
  match t.desc with
  | Local(decl, t2) ->
      let decls,t2' = decomp_locals t2 in
      decl::decls, t2'
  | _ -> [], t

let decomp_assert_desc desc =
  match desc with
  | If(t1, {desc=Const Unit}, {desc=App({desc=Event("fail",_)}, [{desc=Const Unit}])}) -> Some t1
  | _ -> None
let is_assert_desc = Option.is_some -| decomp_assert_desc
