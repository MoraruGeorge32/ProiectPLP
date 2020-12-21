Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.
Open Scope list_scope.

Inductive errn :=
  | error_nat : errn
  | num : nat -> errn.

Inductive errb :=
  | error_bool : errb
  | boolean : bool -> errb.

Coercion num: nat >-> errn.
Coercion boolean: bool >-> errb.

                                          (*AExp*)
Inductive AExp :=
  | avar: string -> AExp
  | anum: errn -> AExp
  | aplus: AExp -> AExp -> AExp
  | asub: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp
  | adiv: AExp -> AExp -> AExp
  | amod: AExp -> AExp -> AExp.

Coercion anum: errn >-> AExp.
Coercion avar: string >-> AExp.

Inductive SExp :=
| Snat: nat -> SExp
| Sstr: string -> SExp
| Scat: string -> string -> SExp
| Slen: string -> SExp
| SStr: string -> nat -> SExp
| Spos: string -> nat -> SExp.

Coercion Snat: nat >-> SExp.
Coercion Sstr: string >-> SExp.

Notation "A -- B" := (Sstr A B)(at level 50, left associativity).
Notation "? A" := (Slen A) (at level 50, left associativity).
Notation " A '? B" := (SStr A B)(at level 50, left associativity).
Notation " A <'> B" := (Spos A B)(at level 50, left associativity).

(*Notații pentru operațiile aritmetice*)

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).

                                          (*BExp*)


Inductive BExp :=
  | berror
  | btrue
  | bfalse
  | bvar: string -> BExp
  | blt : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp.

Notation "A <' B" := (blt A B) (at level 70).
Notation " ! A" := (bnot A)(at level 51, left associativity).
Notation "A & B" := (band A B)(at level 52, left associativity).
Notation "A 'sau' B" := (bor A B)(at level 53, left associativity).

Inductive Stmt:=
  | nat_decl: string -> AExp -> Stmt
  | bool_decl: string -> BExp -> Stmt
  | string_decl: string-> SExp -> Stmt
  | nat_assign : string -> AExp -> Stmt
  | bool_assign : string -> BExp -> Stmt
  | string_assign : string -> SExp -> Stmt
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | for: 
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt.

Notation "A <n> B" := (nat_decl A B)(at level 50).
Notation "A <b> B" := (bool_decl A B)(at level 50).
Notation "A <s> B" := (string_decl A B)(at level 50).
Notation "A <-n B" := (nat_assign A B)(at level 50).
Notation "A <-b B" := (nat_assign A B)(at level 50).
Notation "A <-s B" := (nat_assign A B)(at level 50).
