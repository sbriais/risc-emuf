(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* $Id: gcmap.ml,v 1.1 2005/11/25 17:31:07 sbriais Exp $ *)

type key = Int32.t

type cell = { mutable size : Int32.t; mutable live : bool }

let int32_compare x y = Int32.to_int (Int32.sub (Int32.sub x y) (Int32.sub y x))

let int32_add x y = Int32.add x y

type t =
    Empty
  | Node of t * key * cell * t * int

let height = function
    Empty -> 0
  | Node(_,_,_,_,h) -> h

let create l x d r =
  let hl = height l and hr = height r in
    Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

let bal l x d r =
  let hl = match l with Empty -> 0 | Node(_,_,_,_,h) -> h in
  let hr = match r with Empty -> 0 | Node(_,_,_,_,h) -> h in
    if hl > hr + 2 then begin
      match l with
	  Empty -> invalid_arg "Gcmap.bal"
	| Node(ll, lv, ld, lr, _) ->
	    if height ll >= height lr then
	      create ll lv ld (create lr x d r)
	    else begin
	      match lr with
		  Empty -> invalid_arg "Gcmap.bal"
		| Node(lrl, lrv, lrd, lrr, _)->
		    create (create ll lv ld lrl) lrv lrd (create lrr x d r)
	    end
    end else if hr > hl + 2 then begin
      match r with
	  Empty -> invalid_arg "Gcmap.bal"
	| Node(rl, rv, rd, rr, _) ->
	    if height rr >= height rl then
	      create (create l x d rl) rv rd rr
	    else begin
	      match rl with
		  Empty -> invalid_arg "Gcmap.bal"
		| Node(rll, rlv, rld, rlr, _) ->
		    create (create l x d rll) rlv rld (create rlr rv rd rr)
	    end
    end else
      Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

let empty = Empty

let is_empty = function
  | Empty -> true
  | Node _ -> false

let rec add x data = function
    Empty ->
      Node(Empty, x, data, Empty, 1)
  | Node(l, v, d, r, h) ->
      let c = int32_compare x v in
	if c = 0 then
	  Node(l, x, data, r, h)
	else if c < 0 then
	  bal (add x data l) v d r
	else
	  bal l v d (add x data r)

(* on suppose x < y *)
(*
let rec add_or_join x y data = function
    Empty ->
      Node(Empty, x, data, Empty, 1)
  | Node(l, v, d, r, h) ->
      let c = int32_compare y v in
	if c = 0 then
	  begin
	    d.size <- int32_add data.size d.size;
	    Node(l, x, d, r, h)
	  end
	else if c > 0 then
	  bal l v d (add_or_join x y data r)
	else
	  let c = int32_compare x v in
	    if c = 0 then Node(l,x,data,r,h)
	    else
	      bal (add_or_join x y data l) v d r
*)

let rec find x = function
    Empty ->
      raise Not_found
  | Node(l, v, d, r, _) ->
      let c = int32_compare x v in
	if c = 0 then d
	else find x (if c < 0 then l else r)

let rec mem x = function
    Empty ->
      false
  | Node(l, v, _d, r, _) ->
      let c = int32_compare x v in
	c = 0 || mem x (if c < 0 then l else r)

let rec min_binding = function
    Empty -> raise Not_found
  | Node(Empty, x, d, _r, _) -> (x, d)
  | Node(l, _x, _d, _r, _) -> min_binding l

let rec remove_min_binding = function
    Empty -> invalid_arg "Gcmap.remove_min_elt"
  | Node(Empty, _x, _d, r, _) -> r
  | Node(l, x, d, r, _) -> bal (remove_min_binding l) x d r

let merge t1 t2 =
  match (t1, t2) with
      (Empty, t) -> t
    | (t, Empty) -> t
    | (Node _, Node _) ->
	let (x, d) = min_binding t2 in
	  bal t1 x d (remove_min_binding t2)

let rec remove x = function
    Empty -> Empty
  | Node(l, v, d, r, _h) ->
      let c = int32_compare x v in
	if c = 0 then
	  merge l r
	else if c < 0 then
	  bal (remove x l) v d r
	else
	  bal l v d (remove x r)

let add_or_join x y data map =
  try
    let c = find y map in
      data.size <- int32_add data.size c.size;
      add x data (remove y map)
  with Not_found -> add x data map

let rec iter f = function
    Empty -> ()
  | Node(l, v, d, r, _) ->
      iter f l; f v d; iter f r
