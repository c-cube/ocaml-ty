
type a = A1 | A2 of int | A3 of int * bool | A4 of (bool * int)
type b = a list
type c = { c : b }
type d = { mutable d1: int; d2: bool }
type e
type f = private int
type g = private G1 | G2
type h = private [> `A | `B]

type t

val t: t ty
val t': t ty
