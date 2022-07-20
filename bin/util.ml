open Core

module type MAP = sig
  include Map.S

  val iter2_exn : f:('a -> 'b -> unit) -> 'a t -> 'b t -> unit
  val map2_exn : f:('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val unzip : ('a * 'b) t -> 'a t * 'b t
end

module Make_map (S : Map.Key) : MAP with type Key.t = S.t = struct
  module M = Map.Make (S)
  include M

  let iter2_exn ~f =
    iter2 ~f:(fun ~key:_ ~data ->
        match data with
        | `Both (v1, v2) -> f v1 v2
        | _ -> raise (Invalid_argument "Map.iter2_exn"))
  ;;

  let map2_exn ~f =
    merge ~f:(fun ~key:_ -> function
      | `Both (v1, v2) -> Some (f v1 v2)
      | _ -> raise (Invalid_argument "Map.map2_exn"))
  ;;

  let unzip m =
    fold m ~init:(empty, empty) ~f:(fun ~key ~data:(v1, v2) (acc1, acc2) ->
        Map.add_exn acc1 ~key ~data:v1, Map.add_exn acc2 ~key ~data:v2)
  ;;
end
