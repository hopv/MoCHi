open Util
open Combinator

(** Call trees *)

(** {6 Constructors} *)

type 'a t = {
  name: Idnt.t * int;
  closed: bool;
  ret: (Idnt.t * int) option;
  data: 'a
}

(** {6 Functions on call trees} *)

let make name closed data =
  Zipper.make { name = name; closed = closed; ret = None; data = data } []

let rec path_set_open p =
  match p with
  | Zipper.Top -> Zipper.Top
  | Zipper.Path(up, trs1, nd, trs2) ->
    Zipper.Path(path_set_open up,
                trs1,
                { nd with ret = None(**@todo*); closed = false },
                trs2)

let pr ppf tr =
  let cnt = ref 0 in
  let rec pr_aux ppf (Zipper.Node(nd, trs)) =
    cnt := !cnt + 1;
    Format.fprintf ppf "@[<v>%a" CallId.pr nd.name;
    if trs <> [] then Format.fprintf ppf "@,  %a" (List.pr pr_aux "@,") trs;
    if nd.closed then
      begin
        let x, id =
          match nd.ret with None -> nd.name | Some(x, id) -> x, id
        in
        cnt := !cnt - 1;
        Format.fprintf ppf "@,</%a@@%d>@]" Idnt.pr x id
      end
  in
  pr_aux ppf tr;
  ignore (List.init !cnt (fun _ -> Format.fprintf ppf "@]"))


(** @deprecated ?? *)
let rec path_remove_right p =
  match p with
  | Zipper.Top -> Zipper.Top
  | Zipper.Path(up, trs1, nd, _) ->
    Zipper.Path(path_remove_right up, trs1, nd, [])
