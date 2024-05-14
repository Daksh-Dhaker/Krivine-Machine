type exp = Num of int | Bl of bool | V of string | Plus of exp*exp | Infinite
           | Times of exp*exp | And of exp*exp | Or of exp*exp | Not of exp
           | Eq of exp*exp | Gt of exp*exp | IfTE of exp*exp*exp
           | Pair of exp*exp | Fst of exp | Snd of exp | Lambda of string*exp | Funct of exp*exp
           | Case of (exp)*((exp*exp) list);;

type clos = CLOS of exp*((string*clos) list);;

exception Stuck of (clos*(clos list));;  
exception Operation_error of string*((clos*(clos list)) list) ;;
exception Invalid_ans of (clos*(clos list))

(*--------------------Helper---------------------- *)
let rec look_up gamma x = 
  match gamma with
    | [] -> CLOS(Num 0,gamma)
    | hd::tl -> let (a,b) = hd in 
                if (a = x) then b else look_up tl x


let rec mem g x = 
  match g with 
  | [] -> false
  | hd::tl -> let (a,b) = hd in 
              if (a = x) then true else (mem tl x)


let rec filter g x a =
    match g with
    | [] -> []
    | hd::tl -> let (c,d) = hd in
                if (c = x) then
                  (c,a)::(filter tl x a)
                else
                  hd::(filter tl x a)

let augment g x a = 
    if (mem g x) then (filter g x a) else ((x,a)::g)

(*-------------------------------------------------------- *)

let rec krivine_machine clos stack = 
  match clos,stack with
  | CLOS(Num n,gamma),s -> CLOS(Num n,gamma),s
  | CLOS(Bl b,gamma),s -> CLOS(Bl b,gamma),s
  | CLOS(Pair(e1,e2),gamma),s -> CLOS(Pair(e1,e2),gamma),s
  | CLOS(Infinite,gamma),s -> krivine_machine (CLOS(Infinite,gamma)) s
  | CLOS(Plus(e1,e2),gamma),s ->  let plus c1 c2 = 
                                  match  c1,c2 with
                                  | (CLOS(Num n1,gamma1),s1),(CLOS(Num n2,gamma2),s2) -> CLOS(Num (n1+n2),[])
                                  | _ -> raise (Operation_error("plus",[c1;c2]))
                                  in
                                  krivine_machine (plus (krivine_machine (CLOS(e1,gamma)) []) (krivine_machine (CLOS(e2,gamma)) [])) s

  | CLOS(Times(e1,e2),gamma),s -> let times c1 c2 = 
                                  match  c1,c2 with
                                  | (CLOS(Num n1,gamma1),s1),(CLOS(Num n2,gamma2),s2) -> CLOS(Num (n1*n2),[])
                                  | _ -> raise (Operation_error("times",[c1;c2]))
                                  in
                                  krivine_machine (times (krivine_machine (CLOS(e1,gamma)) []) (krivine_machine (CLOS(e2,gamma)) [])) s

  | CLOS(And(e1,e2),gamma),s -> let and_op c1 c2 = 
                                match  c1,c2 with
                                | (CLOS(Bl b1,gamma1),s1),(CLOS(Bl b2,gamma2),s2) -> CLOS(Bl (b1 && b2),[])
                                | _ -> raise (Operation_error("and",[c1;c2]))
                                in  
                                krivine_machine (and_op (krivine_machine (CLOS(e1,gamma)) []) (krivine_machine (CLOS(e2,gamma)) [])) s

  | CLOS(Or(e1,e2),gamma),s ->  let or_op c1 c2 = 
                                match  c1,c2 with
                                | (CLOS(Bl b1,gamma1),s1),(CLOS(Bl b2,gamma2),s2) -> CLOS(Bl (b1 || b2),[])
                                | _ -> raise (Operation_error("or",[c1;c2]))
                                in
                                krivine_machine (or_op (krivine_machine (CLOS(e1,gamma)) []) (krivine_machine (CLOS(e2,gamma)) [])) s

  | CLOS(Not(e),gamma),s -> let not_op c = 
                            match  c with
                            | (CLOS(Bl b,gamma),s) -> CLOS(Bl (not b),[])
                            | _ -> raise (Operation_error("not",[c]))
                            in
                            krivine_machine (not_op (krivine_machine (CLOS(e,gamma)) [])) s

  | CLOS(Eq(e1,e2),gamma),s ->  let eq c1 c2 = 
                                match  c1,c2 with
                                | (CLOS(n1,gamma1),s1),(CLOS(n2,gamma2),s2) -> CLOS(Bl (n1=n2),[])
                                in
                                krivine_machine (eq (krivine_machine (CLOS(e1,gamma)) []) (krivine_machine (CLOS(e2,gamma)) [])) s

  | CLOS(Gt(e1,e2),gamma),s ->  let gt c1 c2 = 
                                match  c1,c2 with
                                | (CLOS(n1,gamma1),s1),(CLOS(n2,gamma2),s2) -> CLOS(Bl (n1>n2),[])
                                in
                                krivine_machine (gt (krivine_machine (CLOS(e1,gamma)) []) (krivine_machine (CLOS(e2,gamma)) [])) s

  | CLOS(IfTE(e0,e1,e2),gamma),s-> let (CLOS(cond,g),st) = (krivine_machine (CLOS(e0,gamma)) []) in 
                                    if (cond = Bl true) then 
                                      krivine_machine (CLOS(e1,gamma)) s 
                                    else
                                      krivine_machine (CLOS(e2,gamma)) s
  
  | CLOS(Fst(e),gamma),s -> let helper ans g st =
                              match ans with
                              | Pair(a,b) -> krivine_machine (CLOS(a,g)) []
                              | _ -> raise (Stuck(CLOS(Snd(ans),g),st))
                            in
                            let (CLOS(ans,g),st) = krivine_machine (CLOS(e,gamma)) s in
                            helper ans g st

  | CLOS(Snd(e),gamma),s -> let helper ans g st =
                              match ans with
                                | Pair(a,b) -> krivine_machine (CLOS(b,g)) []
                                | _ -> raise (Stuck(CLOS(Snd(ans),g),st))
                            in
                            let (CLOS(ans,g),st) = krivine_machine (CLOS(e,gamma)) s in
                            helper ans g st

  | CLOS(Case(e,l),gamma),s -> let rec compare_case lst x =
                                match lst with 
                                | [] -> Num 0
                                | hd::tl -> let (b,c) = hd in 
                                            let (CLOS(eval_exp,g1),st1) = krivine_machine (CLOS(b,gamma)) [] in
                                            if (eval_exp = x) then c else (compare_case tl x)
                              in
                              let (CLOS(exp,g),st) = (krivine_machine (CLOS(e,gamma)) []) in
                              let ans_exp = (compare_case l exp) in
                              krivine_machine (CLOS(ans_exp,gamma)) s

  | CLOS(Funct(e1,e2),gamma),s -> krivine_machine (CLOS(e1,gamma)) (CLOS(e2,gamma)::s)
  | CLOS(V(x),gamma),s -> krivine_machine  (look_up gamma x) s 
  | CLOS(Lambda(x,e1),gamma),cl::s -> krivine_machine  (CLOS(e1,(augment gamma x cl))) s
  | _,_ -> raise (Stuck(clos,stack))

let cbn exp gamma = 
  let c = CLOS(exp,gamma) in
  let ans = krivine_machine (c) [] in
  let (CLOS(eval_exp,g),st) = ans in
  eval_exp

(*--------------------------------Test-Cases-----------------------------*)
(* krivine_machine (CLOS(e2,gamma)) s
1. let e1 = Plus(V "x",Times(V "y",Plus(V "z",Num 2)));;
   let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
   Ans ->
    krivine_machine (CLOS(e1,g)) [];; -> clos * clos list = (CLOS (Num 1021, []), [])
    cbn e1 g;; -> exp = Num 1021

2. let e1 = And(Bl true,Or(V "b",And(V "c",Not(V "d"))));;
   let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
   Ans ->
    krivine_machine (CLOS(e1,g)) [];; -> clos * clos list = (CLOS (Bl true, []), [])
    cbn e1 g;; -> exp = Bl true

3. let e1 = And(Eq(V "a",Not(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
   let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
   Ans ->
    krivine_machine (CLOS(e1,g)) [];; -> clos * clos list = (CLOS (Bl true, []), [])
    cbn e1 g;; -> exp = Bl true

4. let e1 = And(Eq(V "a",Not(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
   let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
   let e2 = IfTE(e1,Pair(Num 1,V "a"),e1);;
   Ans ->
    krivine_machine (CLOS(e2,g)) [];; ->
      (CLOS (Pair (Num 1, V "a"),[("x", CLOS (Num 1, [])); ("y", CLOS (Num 10, []));("z", CLOS (Num 100, [])); ("a", CLOS (Bl true, []));("b", CLOS (Bl false, [])); ("c", CLOS (Bl true, []));("d", CLOS (Bl false, []))]),[])
    krivine_machine (CLOS(Fst(e2),g)) [];; ->
      (CLOS (Num 1,[("x", CLOS (Num 1, [])); ("y", CLOS (Num 10, []));("z", CLOS (Num 100, [])); ("a", CLOS (Bl true, []));("b", CLOS (Bl false, [])); ("c", CLOS (Bl true, []));("d", CLOS (Bl false, []))]),[])
    krivine_machine (CLOS(Snd(e2),g)) [];; ->
      (CLOS (Bl true, []), [])
    cbn e2 g;; -> exp = Pair (Num 1, V "a")
    cbn (Snd(e2)) g;; -> exp = Bl true
    cbn (Fst(e2)) g;; -> exp = Num 1

5. let e1 = And(Eq(V "a",(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
   let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
   let e2 = IfTE(e1,Pair(Num 1,V "a"),e1);;
   Ans ->
    krivine_machine (CLOS(e2,g)) [];; -> clos * clos list = (CLOS (Bl false, []), [])
    cbn e2 g;; -> exp = Bl false

6. let e1 = And(Eq(V "a",Not(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
   let e2 = IfTE(e1,Pair(Num 1,V "a"),e1);;
   let e3 = Pair(Pair(e1,e2),Snd(Pair(Pair(Num 1,V "x"),V "a")));;
   let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
   krivine_machine (CLOS(e3,g)) [];; ->
    clos * clos list =
(CLOS
  (Pair
    (Pair
      (And (Eq (V "a", Not (Bl false)), Or (V "b", And (V "c", Not (V "d")))),
      IfTE
       (And (Eq (V "a", Not (Bl false)), Or (V "b", And (V "c", Not (V "d")))),
       Pair (Num 1, V "a"),
       And (Eq (V "a", Not (Bl false)), Or (V "b", And (V "c", Not (V "d")))))),
    Snd (Pair (Pair (Num 1, V "x"), V "a"))),
  [("x", CLOS (Num 1, [])); ("y", CLOS (Num 10, []));
   ("z", CLOS (Num 100, [])); ("a", CLOS (Bl true, []));
   ("b", CLOS (Bl false, [])); ("c", CLOS (Bl true, []));
   ("d", CLOS (Bl false, []))]),
 [])
    
    krivine_machine (CLOS((Snd(e3)),g)) [];; -> clos * clos list = (CLOS (Bl true, []), [])
    krivine_machine (CLOS((Fst(Fst(e3))),g)) [];; -> clos * clos list = (CLOS (Bl true, []), [])
    krivine_machine (CLOS(Snd(Snd(Fst(e3))),g)) [];; -> clos * clos list = (CLOS (Bl true, []), [])
    krivine_machine (CLOS(Fst(Snd(Fst(e3))),g)) [];; -> (CLOS (Num 1,[("x", CLOS (Num 1, [])); ("y", CLOS (Num 10, []));("z", CLOS (Num 100, [])); ("a", CLOS (Bl true, []));("b", CLOS (Bl false, [])); ("c", CLOS (Bl true, []));("d", CLOS (Bl false, []))]),[])

    cbn (Snd(e3)) g;; -> exp = Bl true
    cbn (Fst(Fst(e3))) g;; -> exp = Bl true
    cbn (Snd(Snd(Fst(e3)))) g;; -> exp = Bl true
    cbn (Fst(Snd(Fst(e3)))) g;; -> exp = Num 1

    
 7. let e1 = And(Eq(V "a",(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
    let e2 = IfTE(e1,Pair(Num 1,V "a"),e1);;
    let e3 = Pair(Pair(e1,e2),Snd(Pair(Pair(Num 1,V "x"),V "a")));;
    let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
    Ans ->
      krivine_machine (CLOS(Snd(e3),g)) ([]);; -> clos * clos list = (CLOS (Bl true, []), [])
      krivine_machine (CLOS(Fst(Fst(e3)),g)) ([]);; -> clos * clos list = (CLOS (Bl false, []), [])
      krivine_machine (CLOS(Snd(Fst(e3)),g)) ([]);; -> clos * clos list = (CLOS (Bl false, []), [])
      cbn (Snd(e3)) g;; -> exp = Bl true
      cbn (Fst(Fst(e3))) g;; -> exp = Bl false
      cbn (Snd(Fst(e3))) g;; -> exp = Bl false

8.  let e4 = Funct(Lambda("x",Plus(Num 1,V "x")),Num 2);;
    krivine_machine (CLOS(e4,g)) ([]);; -> clos * clos list = (CLOS (Num 3, []), [])

9.  let e4 = Funct(Lambda("d",Funct(Lambda("c",(Pair(V "c",V "d"))),Plus(Num 1,V "x"))),V "y");;
    let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
    Ans ->
      krivine_machine (CLOS(Fst(e4),g)) ([]);; -> clos * clos list = (CLOS (Num 2, []), [])
      krivine_machine (CLOS(Snd(e4),g)) ([]);; -> clos * clos list = (CLOS (Num 10, []), [])
      cbn (Fst(e4)) g;; -> exp = Num 2
      cbn (Snd(e4)) g;; -> exp = Num 10

10. let e4 = Funct(Lambda("x",Plus(V "x",Num 1)),Snd(Funct(Lambda("d",Funct(Lambda("c",(Pair(V "c",V "d"))),Num 1)),V "y")));;
    let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
    Ans ->
      krivine_machine (CLOS((e4),g)) ([]);; -> clos * clos list = (CLOS (Num 11, []), [])
      cbn ((e4)) g;; -> exp = Num 11

11. let e1 = Case(Plus(Num 1,Times(Num 2,Num 3)),[(Plus(V "x",Num 4),Num 1);(Times(V "x",V "y"),Num 2);(Plus(Num 6,V "x"),Num 3);(Plus(Num 1,Num 2),Num 4)]);;
    let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
    Ans -> 
      krivine_machine (CLOS((e1),g)) ([]);; -> 
        clos * clos list =(CLOS (Num 3,[("x", CLOS (Num 1, [])); ("y", CLOS (Num 10, []));("z", CLOS (Num 100, [])); ("a", CLOS (Bl true, []));("b", CLOS (Bl false, [])); ("c", CLOS (Bl true, []));("d", CLOS (Bl false, []))]),[])
      cbn (e1) g;; -> exp = Num 3

12. let e1 = Case(Plus(Num 1,Times(Num 2,Num 3)),[(Plus(V "x",Num 4),Or(V "a",V "b"));(Times(V "x",V "y"),And(V "a",V "d"));(Plus(Num 6,V "x"),Plus(Num 1,Num 33));(Plus(Num 1,Num 2),Num 4)]);;
    let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
    Ans ->
      krivine_machine (CLOS((e1),g)) ([]);; -> clos * clos list = (CLOS (Num 34, []), [])

13. let e1 = Case(Plus(Num 1,Times(Num 1,Num 9)),[(Plus(V "x",Num 4),Or(V "a",V "b"));(Times(V "x",V "y"),And(V "a",V "d"));(Plus(Num 6,V "x"),Plus(Num 1,Num 33));(Plus(Num 1,Num 2),Num 4)]);;
    let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
    Ans ->
      krivine_machine (CLOS((e1),g)) ([]);; -> clos * clos list = (CLOS (Bl false, []), [])
      cbn (e1) g;; -> exp = Bl false

14. let e1 = Case(Plus(Num 1,Times(Num 1,Num 4)),[(Plus(V "x",Num 4),Or(V "a",V "b"));(Times(V "x",V "y"),And(V "a",V "d"));(Plus(Num 6,V "x"),Plus(Num 1,Num 33));(Plus(Num 1,Num 2),Num 4)]);;
    let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
    Ans ->
      krivine_machine (CLOS((e1),g)) ([]);; -> clos * clos list = (CLOS (Bl true, []), [])
      cbn (e1) g;; -> exp = Bl true

15. let e1 = Pair(Plus(Num 1,Num 2),Infinite);;
    let g = [("x",CLOS(Num 1,[]));("y",CLOS(Num 10,[]));("z",CLOS(Num 100,[]));("a",CLOS(Bl true,[]));("b",CLOS(Bl false,[]));("c",CLOS(Bl true,[]));("d",CLOS(Bl false,[]))];;
    Ans ->
      krivine_machine (CLOS(e1,g)) [];; -> 
        clos * clos list =(CLOS (Pair (Plus (Num 1, Num 2), Infinite),[("x", CLOS (Num 1, [])); ("y", CLOS (Num 10, []));("z", CLOS (Num 100, [])); ("a", CLOS (Bl true, []));("b", CLOS (Bl false, [])); ("c", CLOS (Bl true, []));("d", CLOS (Bl false, []))]),[])
      krivine_machine (CLOS(Fst(e1),g)) [];; -> clos * clos list = (CLOS (Num 3, []), [])
      
      cbn e1 g;; -> exp = Pair (Plus (Num 1, Num 2), Infinite)
      cbn (Fst(e1)) g;; -> exp = Num 3

16. let e1 = Funct(Lambda("x",Funct(Lambda("y",V "x"),Infinite)),Plus(Num 1,Num 2));;
    Ans ->
      krivine_machine (CLOS((e1),g)) [];; -> clos * clos list = (CLOS (Num 3, []), [])
      cbn e1 g;; -> exp = Num 3

17. let e1 = IfTE(And(Bl true,Bl false),Infinite,Times(Num 5,Num 2));;
    Ans ->
      krivine_machine (CLOS((e1),g)) [];; -> clos * clos list = (CLOS (Num 10, []), [])
      cbn e1 g;; -> exp = Num 10

18. let e1 = Case(Plus(Num 2,Num 3),[(Num 2,Bl false);(Num 3,Infinite);(Num 5,Bl true);(Num 4,Infinite)]);;
    Ans ->
      krivine_machine (CLOS((e1),g)) [];; ->
      clos * clos list =(CLOS (Bl true,[("x", CLOS (Num 1, [])); ("y", CLOS (Num 10, []));("z", CLOS (Num 100, [])); ("a", CLOS (Bl true, []));("b", CLOS (Bl false, [])); ("c", CLOS (Bl true, []));("d", CLOS (Bl false, []))]),[])
      cbn e1 g;; -> exp = Bl true
*)
(*-----------------------------------------------------------------------*)
