(* CMSC 330 / Spring 2017 / Project 4 (0, None, 1);(1, Some 'a', 11);(11, None, 3);(3, None, 11);(11, None, 12);(12, Some 'a', 14);(14, Some 'a', 13);(13, None, 3);(3, None, 5);(0, None, 2);(2, Some 'b', 6);(6, Some 'b', 7);(7, None, 4);(4, None, 7);(7, None, 8);(8, Some 'b', 10);(10, Some 'b', 9);(9, None, 4);(4, None, 5)*)
(* Name: Josiah Boyle *)
open List
open String
open Pervasives

type transition = int * char option * int
type stats = {num_states : int; num_finals : int; outgoing_counts : (int * int) list}

let get_next_gen () =
  let x = ref 0 in
  (fun () -> let r = !x in x := !x + 1; r)

let next = get_next_gen ()

(* YOUR CODE BEGINS HERE *)


type nfa_t = int * transition list * int list
(*start state, set of final states, transitions*)

let make_nfa ss fs ts = (ss, ts, fs)
;;

let rec eps_edges n g a = match g with
    [] -> a
    | (x, Some y, z)::t -> eps_edges n t a
    | (x, None, z)::t -> if x = n then (eps_edges n t (z::a)) else (eps_edges n t a)
;;

let rec check c e = match e with
      [] -> false
    | (x, None, z)::t -> if (c = x) || (c = z) then true else check c t
    | (x, Some y, z)::t -> if (c = x) || (c = z) then true else check c t
;;

let rec reach t l g = match l with
    [] -> t
    | h::tail -> reach (if (List.mem h t) = false then (reach (h::t) (eps_edges h g []) g) else t) tail g
;;

let rec e_closure_helper m l t = match l with
    [] -> t
    |h::tail -> if (check h m) = false then t else e_closure_helper m tail (reach t (eps_edges h m [h]) m)
;;

let e_closure m l = match m with
    (x, y, z) -> e_closure_helper y l []
;;

let move_help t e c = List.fold_left (fun x y -> (match y with (a,Some b,w) -> (if e = a && b = c && List.mem w x = false then w::x else x) | (_,None,_) -> x)) [] t
;;

let move m l c = match m with (_,t,_) -> List.sort_uniq compare (List.fold_left (fun x y -> (move_help t y c) @ x) [] l)
;;

let rec str_to_list s = match s with 
        "" -> []
        | c -> (String.get s 0)::(str_to_list(String.sub s 1 (String.length s - 1)))
;; 

let rec elem x a = match a with
    [] -> false
    | h::t -> if x = h then true else elem x t
;;

let rec intersection a b = match a with
    [] -> []
    | h::t -> if (elem h b) = true then h::(intersection t b) else intersection t b
;;

let rec remove x a = match a with
    [] -> []
    | h::t -> if h = x then t else h :: remove x t
;;

let rec eq a b = match a, b with
    [], [] -> true
    | [], h::t -> false
    | h::t, [] -> false
    | h::t, l -> if elem h l = false then false else eq t (remove h l)
;;

let rec accept_helper m s c y = match s with
    [] -> if (intersection (e_closure m c) y) = [] then false else true
    |h::t -> if (eq (move m (e_closure m c) h) []) = false then (accept_helper m t (move m (e_closure m c) h) y) else false

let accept m s = match m with
    (x, y, z) -> accept_helper m (str_to_list s) (e_closure m [x]) z

let states_list t = List.fold_left (fun x y -> match y with (a,_,c) -> if List.mem a x = false && List.mem c x = false then a::c::x
                                       else if List.mem a x = false then a::x else if List.mem c x = false then c::x else x) [] t
;;

let stat_help e t = List.fold_left (fun x y -> match y with (a,_,_) -> if e = a then x+1 else x) 0 t
;;

let outgoing_counts_help s t= List.sort compare (List.fold_left (fun x y -> (stat_help y t)::x) [] s)
;;

let count e lst = match lst with
    [] -> 0
    | (h::t) -> List.fold_left (fun x y -> if (e = y) then x + 1 else x) 0 lst
;;

let rec count_help l i = match l with
    [] -> []
    | h::t -> if (count i l) != 0 then (i,count i l)::count_help t (i+1) else count_help t (i+1)
;;

let stats m = match m with (s,t,f) -> {num_states = List.length (states_list t); 
                                       num_finals = List.length f; 
                                       outgoing_counts = count_help (outgoing_counts_help (states_list t) t) 0}
;;

let get_start m = match m with (s,_,_) -> s
let get_finals m = match m with (_,_,f) -> f
let get_transitions m = match m with (_,t,_) -> t