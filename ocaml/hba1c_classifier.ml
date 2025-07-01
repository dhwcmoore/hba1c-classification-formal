
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

module Z =
 struct
  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True
 end

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| Nil -> None
| Cons (x, tl) -> (match f x with
                   | True -> Some x
                   | False -> find f tl)

type q = { qnum : z; qden : positive }

(** val qle_bool : q -> q -> bool **)

let qle_bool x y =
  Z.leb (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

type 'a interval = ('a, 'a option) prod

(** val in_interval : q -> q interval -> bool **)

let in_interval x = function
| Pair (l, ro) ->
  (match qle_bool l x with
   | True -> (match ro with
              | Some r -> negb (qle_bool r x)
              | None -> True)
   | False -> False)

(** val make_classifier : (q interval, string) prod list -> q -> string **)

let make_classifier bounds x =
  match find (fun pat -> let Pair (i, _) = pat in in_interval x i) bounds with
  | Some p -> let Pair (_, label) = p in label
  | None ->
    String ((Ascii (True, False, True, False, True, False, True, False)),
      (String ((Ascii (False, True, True, True, False, True, True, False)),
      (String ((Ascii (True, True, False, True, False, True, True, False)),
      (String ((Ascii (False, True, True, True, False, True, True, False)),
      (String ((Ascii (True, True, True, True, False, True, True, False)),
      (String ((Ascii (True, True, True, False, True, True, True, False)),
      (String ((Ascii (False, True, True, True, False, True, True, False)),
      EmptyString)))))))))))))

(** val hba1c_bounds : (q interval, string) prod list **)

let hba1c_bounds =
  Cons ((Pair ((Pair ({ qnum = (Zpos (XI (XO (XO (XI (XI XH)))))); qden = (XO
    (XI (XO XH))) }, (Some { qnum = (Zpos (XI (XO (XO (XO (XO (XO XH)))))));
    qden = (XO (XI (XO XH))) }))), (String ((Ascii (False, False, False,
    False, True, False, True, False)), (String ((Ascii (False, True, False,
    False, True, True, True, False)), (String ((Ascii (True, False, True,
    False, False, True, True, False)), (String ((Ascii (True, False, True,
    True, False, True, False, False)), (String ((Ascii (False, False, True,
    False, False, False, True, False)), (String ((Ascii (True, False, False,
    True, False, True, True, False)), (String ((Ascii (True, False, False,
    False, False, True, True, False)), (String ((Ascii (False, True, False,
    False, False, True, True, False)), (String ((Ascii (True, False, True,
    False, False, True, True, False)), (String ((Ascii (False, False, True,
    False, True, True, True, False)), (String ((Ascii (True, False, True,
    False, False, True, True, False)), (String ((Ascii (True, True, False,
    False, True, True, True, False)), EmptyString)))))))))))))))))))))))))),
    (Cons ((Pair ((Pair ({ qnum = (Zpos (XI (XO (XO (XO (XO (XO XH)))))));
    qden = (XO (XI (XO XH))) }, (Some { qnum = (Zpos (XO (XO (XI (XO (XO (XI
    XH))))))); qden = (XO (XI (XO XH))) }))), (String ((Ascii (False, False,
    True, False, False, False, True, False)), (String ((Ascii (True, False,
    False, True, False, True, True, False)), (String ((Ascii (True, False,
    False, False, False, True, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (True, False,
    True, False, False, True, True, False)), (String ((Ascii (False, False,
    True, False, True, True, True, False)), (String ((Ascii (True, False,
    True, False, False, True, True, False)), (String ((Ascii (True, True,
    False, False, True, True, True, False)), EmptyString)))))))))))))))))),
    Nil)))

(** val classify_hba1c : q -> string **)

let classify_hba1c =
  make_classifier hba1c_bounds
