From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language.
From iris.heap_lang Require Export locations.
From Coq.omega Require Omega.
Set Default Proof Using "Type".


Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module cf_lang.
Open Scope Z_scope.

(** Expressions and vals. *)
Definition proph_id := positive.

(** We have a notion of "poison" as a variant of unit that may not be compared
with anything. This is useful for erasure proofs: if we erased things to unit,
[<erased> == unit] would evaluate to true after erasure, changing program
behavior. So we erase to the poison value instead, making sure that no legal
comparisons could be affected. *)
Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitPoison
  | LitLoc (l : loc).
   (* | LitProphecy (p: proph_id). *)
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp. (* Pointer offset *)

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Concurrency *)
  | Fork (e : expr)
  (* Heap *)
  | AllocN (e1 e2 : expr) (* array length (positive number), initial value *)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr) (* Compare-exchange *)
  | FAA (e1 : expr) (e2 : expr) (* Fetch-and-add *)
  (* Prophecy *)
  (* | NewProph *)
  (* | Resolve (e0 : expr) (e1 : expr) (e2 : expr) (* wrapped expr, proph, val *) *)
  (* MARK: Control Flow: Loop *)
  | LoopB (eb : expr) (e : expr)    (* loop body: original loop body, expression remains in the current iteration *)
  | EBreak (e : expr)
  | EContinue
  (* MARK: Control Flow: Return *)
  | Call (e : expr) (* function invocation: function body *)
  | EReturn (e : expr)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Inductive sval :=
  | SVal (v : val)
  | SBreak (v : val)
  | SContinue
  | SReturn (v : val).

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.
Bind Scope sval_scope with sval.

(** An observation associates a prophecy variable (identifier) to a pair of
values. The first value is the one that was returned by the (atomic) operation
during which the prophecy resolution happened (typically, a boolean when the
wrapped operation is a CmpXchg). The second value is the one that the prophecy
variable was actually resolved to. *)
Definition observation : Set := proph_id * (val * val).

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Definition of_sval (sv : sval) : expr :=
  match sv with 
  | SVal v => Val v
  | SBreak v => EBreak $ Val v
  | SContinue => EContinue
  | SReturn v => EReturn $ Val v
  end.

Definition to_sval (e : expr) : option sval :=
  match e with
  | Val v => Some $ SVal v
  | EBreak (Val v) => Some $ SBreak v
  | EContinue => Some SContinue
  | EReturn (Val v) => Some $ SReturn v
  | _ => None
  end.

Inductive is_cf_expr : expr -> Prop :=
| break_is_cfe e: is_cf_expr $ EBreak e
| continue_is_cfe: is_cf_expr EContinue
| return_is_cfe e: is_cf_expr $ EReturn e.

Inductive is_cf_terminal : expr -> Prop :=
  | break_is_cft v: is_cf_terminal $ EBreak (Val v)
  | continue_is_cft: is_cf_terminal EContinue
  | return_is_cft v: is_cf_terminal $ EReturn (Val v).

(** We assume the following encoding of values to 64-bit words: The least 3
significant bits of every word are a "tag", and we have 61 bits of payload,
which is enough if all pointers are 8-byte-aligned (common on 64bit
architectures). The tags have the following meaning:

0: Payload is the data for a LitV (LitInt _).
1: Payload is the data for a InjLV (LitV (LitInt _)).
2: Payload is the data for a InjRV (LitV (LitInt _)).
3: Payload is the data for a LitV (LitLoc _).
4: Payload is the data for a InjLV (LitV (LitLoc _)).
4: Payload is the data for a InjRV (LitV (LitLoc _)).
6: Payload is one of the following finitely many values, which 61 bits are more
   than enough to encode:
   LitV LitUnit, InjLV (LitV LitUnit), InjRV (LitV LitUnit),
   LitV LitPoison, InjLV (LitV LitPoison), InjRV (LitV LitPoison),
   LitV (LitBool _), InjLV (LitV (LitBool _)), InjRV (LitV (LitBool _)).
7: Value is boxed, i.e., payload is a pointer to some read-only memory area on
   the heap which stores whether this is a RecV, PairV, InjLV or InjRV and the
   relevant data for those cases. However, the boxed representation is never
   used if any of the above representations could be used.

Ignoring (as usual) the fact that we have to fit the infinite Z/loc into 61
bits, this means every value is machine-word-sized and can hence be atomically
read and written.  Also notice that the sets of boxed and unboxed values are
disjoint. *)
Definition lit_is_unboxed (l: base_lit) : Prop :=
  match l with
  (** Disallow comparing (erased) prophecies with (erased) prophecies, by
  considering them boxed. *)
  (* | LitProphecy _  *)
  | LitPoison => False
  | _ => True
  end.
Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => lit_is_unboxed l
  | InjLV (LitV l) => lit_is_unboxed l
  | InjRV (LitV l) => lit_is_unboxed l
  | _ => False
  end.

Instance lit_is_unboxed_dec l : Decision (lit_is_unboxed l).
Proof. destruct l; simpl; exact (decide _). Defined.
Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | | [] | [] ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Arguments vals_compare_safe !_ !_ /.

(** The state: heaps of vals. *)
Record state : Type := {
  heap: gmap loc val;
  used_proph_id: gset proph_id;
}.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof.
  destruct e=>//=;
  try destruct e=>//=; intros [= <-]; auto.
Qed.

Lemma to_of_sval v : to_sval (of_sval v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_sval e v : to_sval e = Some v -> of_sval v = e.
Proof.
  destruct e=>//=;
  try destruct e=>//=; intros [= <-]; auto.
Qed.

Instance of_sval_inj : Inj (=) (=) of_sval.
Proof.
  intros ??.
  destruct x=>//=;
  destruct y=>//=;
  congruence.
Qed.

Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Instance expr_eq_dec : EqDecision expr.
Proof.
  refine (
   fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
     match e1, e2 with
     | Val v, Val v' => cast_if (decide (v = v'))
     | Var x, Var x' => cast_if (decide (x = x'))
     | Rec f x e, Rec f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | App e1 e2, App e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
     | BinOp o e1 e2, BinOp o' e1' e2' =>
        cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
     | If e0 e1 e2, If e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Pair e1 e2, Pair e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Fst e, Fst e' => cast_if (decide (e = e'))
     | Snd e, Snd e' => cast_if (decide (e = e'))
     | InjL e, InjL e' => cast_if (decide (e = e'))
     | InjR e, InjR e' => cast_if (decide (e = e'))
     | Case e0 e1 e2, Case e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Fork e, Fork e' => cast_if (decide (e = e'))
     | AllocN e1 e2, AllocN e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Load e, Load e' => cast_if (decide (e = e'))
     | Store e1 e2, Store e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | CmpXchg e0 e1 e2, CmpXchg e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | FAA e1 e2, FAA e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     (* | NewProph, NewProph => left _ *)
     (* | Resolve e0 e1 e2, Resolve e0' e1' e2' => *)
        (* cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2')) *)
     (* MARK: new rules for new expressions *)
     | LoopB eb e, LoopB eb' e' =>
        cast_if_and (decide (eb = eb')) (decide (e = e'))
     | EBreak e, EBreak e' => cast_if (decide (e = e'))
     | EContinue, EContinue => left _
     | Call e, Call e' => cast_if (decide (e = e'))
     | EReturn e, EReturn e' => cast_if (decide (e = e'))
     | _, _ => right _
     end
   with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
     match v1, v2 with
     | LitV l, LitV l' => cast_if (decide (l = l'))
     | RecV f x e, RecV f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | PairV e1 e2, PairV e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | InjLV e, InjLV e' => cast_if (decide (e = e'))
     | InjRV e, InjRV e' => cast_if (decide (e = e'))
     | _, _ => right _
     end
   for go); try (clear go gov; abstract intuition congruence).
Defined.
Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.
Instance sval_eq_dec : EqDecision sval.
Proof. solve_decision. Defined.

Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => (inl (inl n))
  | LitBool b => (inl (inr b))
  | LitUnit => (inr (inl false))
  | LitPoison => (inr (inl true))
  | LitLoc l => (inr (inr l))
  (* | LitProphecy p => (inr (inl false), Some p) *)
  end) (λ l, match l with
  | (inl (inl n)) => LitInt n
  | (inl (inr b)) => LitBool b
  | (inr (inl false)) => LitUnit
  | (inr (inl true)) => LitPoison
  | (inr (inr l)) => LitLoc l
  (* | (_, Some p) => LitProphecy p *)
  end) _); by intros [].
Qed.
Instance un_op_finite : Countable un_op.
Proof.
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 end)
  (λ n, match n with 0 => NegOp | _ => MinusUnOp end) _); by intros [].
Qed.
Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12 | OffsetOp => 13
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | 12 => EqOp | _ => OffsetOp
  end) _); by intros [].
Qed.
Instance expr_countable : Countable expr.
Proof.
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [gov v]
     | Var x => GenLeaf (inl (inl x))
     | Rec f x e => GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | App e1 e2 => GenNode 2 [go e1; go e2]
     | UnOp op e => GenNode 3 [GenLeaf (inr (inr (inl op))); go e]
     | BinOp op e1 e2 => GenNode 4 [GenLeaf (inr (inr (inr op))); go e1; go e2]
     | If e0 e1 e2 => GenNode 5 [go e0; go e1; go e2]
     | Pair e1 e2 => GenNode 6 [go e1; go e2]
     | Fst e => GenNode 7 [go e]
     | Snd e => GenNode 8 [go e]
     | InjL e => GenNode 9 [go e]
     | InjR e => GenNode 10 [go e]
     | Case e0 e1 e2 => GenNode 11 [go e0; go e1; go e2]
     | Fork e => GenNode 12 [go e]
     | AllocN e1 e2 => GenNode 13 [go e1; go e2]
     | Load e => GenNode 14 [go e]
     | Store e1 e2 => GenNode 15 [go e1; go e2]
     | CmpXchg e0 e1 e2 => GenNode 16 [go e0; go e1; go e2]
     | FAA e1 e2 => GenNode 17 [go e1; go e2]
     (* | NewProph => GenNode 18 [] *)
     (* | Resolve e0 e1 e2 => GenNode 19 [go e0; go e1; go e2] *)
     (* MARK: new rules for new expressions *)
     | LoopB eb e => GenNode 20 [go eb; go e]
     | EBreak e => GenNode 21 [go e]
     | EContinue => GenNode 22 []
     | Call e => GenNode 23 [go e]
     | EReturn e => GenNode 24 [go e]
     end
   with gov v :=
     match v with
     | LitV l => GenLeaf (inr (inl l))
     | RecV f x e =>
        GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
     | InjLV v => GenNode 2 [gov v]
     | InjRV v => GenNode 3 [gov v]
     end
   for go).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [v] => Val (gov v)
     | GenLeaf (inl (inl x)) => Var x
     | GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => Rec f x (go e)
     | GenNode 2 [e1; e2] => App (go e1) (go e2)
     | GenNode 3 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
     | GenNode 4 [GenLeaf (inr (inr (inr op))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 6 [e1; e2] => Pair (go e1) (go e2)
     | GenNode 7 [e] => Fst (go e)
     | GenNode 8 [e] => Snd (go e)
     | GenNode 9 [e] => InjL (go e)
     | GenNode 10 [e] => InjR (go e)
     | GenNode 11 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
     | GenNode 12 [e] => Fork (go e)
     | GenNode 13 [e1; e2] => AllocN (go e1) (go e2)
     | GenNode 14 [e] => Load (go e)
     | GenNode 15 [e1; e2] => Store (go e1) (go e2)
     | GenNode 16 [e0; e1; e2] => CmpXchg (go e0) (go e1) (go e2)
     | GenNode 17 [e1; e2] => FAA (go e1) (go e2)
     (* | GenNode 18 [] => NewProph *)
     (* | GenNode 19 [e0; e1; e2] => Resolve (go e0) (go e1) (go e2) *)
     (* MARK: new rules for new expressions *)
     | GenNode 20 [eb; e] => LoopB (go eb) (go e)
     | GenNode 21 [e] => EBreak (go e)
     | GenNode 22 [] => EContinue
     | GenNode 23 [e] => Call (go e)
     | GenNode 24 [e] => EReturn (go e)
     | _ => Val $ LitV LitUnit (* dummy *)
     end
   with gov v :=
     match v with
     | GenLeaf (inr (inl l)) => LitV l
     | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => RecV f x (go e)
     | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
     | GenNode 2 [v] => InjLV (gov v)
     | GenNode 3 [v] => InjRV (gov v)
     | _ => LitV LitUnit (* dummy *)
     end
   for go).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
 - destruct e as [v | | | | | | | | | | | | | | | | | | | | | | | ]; simpl; f_equal;
     [exact (gov v)|done..].
 - destruct v; by f_equal.
Qed.
Instance val_countable : Countable val.
Proof.
  refine (inj_countable of_val to_val _); auto.
Qed.
Instance sval_countable : Countable sval.
Proof. refine (inj_countable of_sval to_sval _); auto using to_of_sval. Qed.

Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; used_proph_id := inhabitant |}.
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.


(* MARK: ctx' is used for isolating an expression from a larger one.
 DIFFERENT from ectx, an expression can be expressed by multiple ctx'. *)
Inductive ctx' :=
  | EmptyCtx'
  | AppLCtx' (K : ctx') (e2 : expr)
  | AppRCtx' (e1 : expr) (K : ctx')
  | UnOpCtx' (op : un_op) (K : ctx')
  | BinOpLCtx' (op : bin_op) (K : ctx') (e2 : expr)
  | BinOpRCtx' (op : bin_op) (e1 : expr) (K : ctx')
  | IfCtx' (K : ctx') (e1 e2 : expr)
  | PairLCtx' (K : ctx') (e2 : expr)
  | PairRCtx' (e1 : expr) (K : ctx')
  | FstCtx' (K : ctx')
  | SndCtx' (K : ctx')
  | InjLCtx' (K : ctx')
  | InjRCtx' (K : ctx')
  | CaseCtx' (K : ctx') (e1 : expr) (e2 : expr)
  | AllocNLCtx' (K : ctx') (e2 : expr)
  | AllocNRCtx' (e1 : expr) (K : ctx')
  | LoadCtx' (K : ctx')
  | StoreLCtx' (K : ctx') (e2 : expr)
  | StoreRCtx' (e1 : expr) (K : ctx')
  | CmpXchgLCtx' (K : ctx') (e1 : expr) (e2 : expr)
  | CmpXchgMCtx' (e0 : expr) (K : ctx') (e2 : expr)
  | CmpXchgRCtx' (e0 : expr) (e1 : expr) (K : ctx')
  | FaaLCtx' (K : ctx') (e2 : expr)
  | FaaRCtx' (e1 : expr) (K : ctx')
  (* TODO: possible problems with the resolve context *)
  (* | ResolveLCtx' (K : ctx') (e1 : expr) (e2 : expr) *)
  (* | ResolveMCtx' (e0 : expr) (K : ctx') (e2 : expr) *)
  (* | ResolveRCtx' (e0 : expr) (e1 : expr) (K : ctx') *)
  (* MARK: new contexts *)
  | LoopBCtx' (eb : expr) (K : ctx')
  | BreakCtx' (K : ctx')
  | CallCtx' (K : ctx')
  | ReturnCtx' (K : ctx').

Fixpoint comp_ctx' (K1 K2 : ctx') : ctx' :=
  match K1 with
  | EmptyCtx' => K2
  | AppLCtx' K e2 => AppLCtx' (comp_ctx' K K2) e2
  | AppRCtx' e1 K => AppRCtx' e1 (comp_ctx' K K2)
  | UnOpCtx' op K => UnOpCtx' op (comp_ctx' K K2)
  | BinOpLCtx' op K e2 => BinOpLCtx' op (comp_ctx' K K2) e2
  | BinOpRCtx' op e1 K => BinOpRCtx' op e1 (comp_ctx' K K2)
  | IfCtx' K e1 e2 => IfCtx' (comp_ctx' K K2) e1 e2
  | PairLCtx' K e2 => PairLCtx' (comp_ctx' K K2) e2
  | PairRCtx' e1 K => PairRCtx' e1 (comp_ctx' K K2)
  | FstCtx' K => FstCtx' (comp_ctx' K K2)
  | SndCtx' K => SndCtx' (comp_ctx' K K2)
  | InjLCtx' K => InjLCtx' (comp_ctx' K K2)
  | InjRCtx' K => InjRCtx' (comp_ctx' K K2)
  | CaseCtx' K e1 e2 => CaseCtx' (comp_ctx' K K2) e1 e2
  | AllocNLCtx' K e2 => AllocNLCtx' (comp_ctx' K K2) e2
  | AllocNRCtx' e1 K => AllocNRCtx' e1 (comp_ctx' K K2)
  | LoadCtx' K => LoadCtx' (comp_ctx' K K2)
  | StoreLCtx' K e2 => StoreLCtx' (comp_ctx' K K2) e2
  | StoreRCtx' e1 K => StoreRCtx' e1 (comp_ctx' K K2)
  | CmpXchgLCtx' K e1 e2 => CmpXchgLCtx' (comp_ctx' K K2) e1 e2
  | CmpXchgMCtx' e0 K e2 => CmpXchgMCtx' e0 (comp_ctx' K K2) e2
  | CmpXchgRCtx' e0 e1 K => CmpXchgRCtx' e0 e1 (comp_ctx' K K2)
  | FaaLCtx' K e2 => FaaLCtx' (comp_ctx' K K2) e2
  | FaaRCtx' e1 K => FaaRCtx' e1 (comp_ctx' K K2)
  (* TODO: possible problems with the resolve context *)
  (* | ResolveLCtx' K e1 e2 => ResolveLCtx' (comp_ctx' K K2) e1 e2 *)
  (* | ResolveMCtx' e0 K e2 => ResolveMCtx' e0 (comp_ctx' K K2) e2 *)
  (* | ResolveRCtx' e0 e1 K => ResolveRCtx' e0 e1 (comp_ctx' K K2) *)
  (* MARK: new contexts *)
  | LoopBCtx' eb K => LoopBCtx' eb (comp_ctx' K K2)
  | BreakCtx' K => BreakCtx' (comp_ctx' K K2)
  | CallCtx' K => CallCtx' (comp_ctx' K K2)
  | ReturnCtx' K => ReturnCtx' (comp_ctx' K K2)
  end.

(* MARK: impenetrable contexts *)
Inductive impenetrable_ctx' : expr -> ctx' -> Prop :=
  | BreakImpenLoop' e eb K:
    impenetrable_ctx' (EBreak e) (LoopBCtx' eb K)
  | BreakImpenCall' e K:
    impenetrable_ctx' (EBreak e) (CallCtx' K)
  | ContinueImpenLoop' eb K:
    impenetrable_ctx' EContinue (LoopBCtx' eb K)
  | ContinueImpenCall' K:
    impenetrable_ctx' EContinue (CallCtx' K)
  | ReturnImpenCall' e K:
    impenetrable_ctx' (EReturn e) (CallCtx' K)
  | CompImpenCtx' e K K':
    impenetrable_ctx' e K ->
    impenetrable_ctx' e (comp_ctx' K' K).

(* MARK: scope contexts *)
Inductive scope_ctx' : expr -> ctx' -> Prop :=
  | LoopScopeBreak' e eb K:
    ~ impenetrable_ctx' (EBreak e) K ->
    scope_ctx' (EBreak e) (LoopBCtx' eb K)
  | LoopScopeContinue' eb K:
    ~ impenetrable_ctx' EContinue K ->
    scope_ctx' EContinue (LoopBCtx' eb K)
  | CallScopeReturn' e K:
    ~ impenetrable_ctx' (EReturn e) K ->
    scope_ctx' (EReturn e) (CallCtx' K)
  | CompScopeCtx' e K K':
    scope_ctx' e K ->
    scope_ctx' e (comp_ctx' K' K).

Fixpoint fill' (K : ctx') (e : expr) : expr :=
  match K with
  | EmptyCtx' => e
  | AppLCtx' K e2 => App (fill' K e) e2
  | AppRCtx' e1 K => App e1 (fill' K e)
  | UnOpCtx' op K => UnOp op (fill' K e)
  | BinOpLCtx' op K e2 => BinOp op (fill' K e) e2
  | BinOpRCtx' op e1 K => BinOp op e1 (fill' K e)
  | IfCtx' K e1 e2 => If (fill' K e) e1 e2
  | PairLCtx' K e2 => Pair (fill' K e) e2
  | PairRCtx' e1 K => Pair e1 (fill' K e)
  | FstCtx' K => Fst (fill' K e)
  | SndCtx' K => Snd (fill' K e)
  | InjLCtx' K => InjL (fill' K e)
  | InjRCtx' K => InjR (fill' K e)
  | CaseCtx' K e1 e2 => Case (fill' K e) e1 e2
  | AllocNLCtx' K e2 => AllocN (fill' K e) e2
  | AllocNRCtx' e1 K => AllocN e1 (fill' K e)
  | LoadCtx' K => Load (fill' K e)
  | StoreLCtx' K e2 => Store (fill' K e) e2
  | StoreRCtx' e1 K => Store e1 (fill' K e)
  | CmpXchgLCtx' K e1 e2 => CmpXchg (fill' K e) e1 e2
  | CmpXchgMCtx' e0 K e2 => CmpXchg e0 (fill' K e) e2
  | CmpXchgRCtx' e0 e1 K => CmpXchg e0 e1 (fill' K e)
  | FaaLCtx' K e2 => FAA (fill' K e) e2
  | FaaRCtx' e1 K => FAA e1 (fill' K e)
  (* | ResolveLCtx' K e1 e2 => Resolve (fill' K e) e1 e2 *)
  (* | ResolveMCtx' ex K e2 => Resolve ex (fill' K e) e2 *)
  (* | ResolveRCtx' ex e1 K => Resolve ex e1 (fill' K e) *)
  (* MARK: new rules for new contexts *)
  | LoopBCtx' eb K => LoopB eb (fill' K e)
  | BreakCtx' K => EBreak (fill' K e)
  | CallCtx' K => Call (fill' K e)
  | ReturnCtx' K => EReturn (fill' K e)
  end.

(* MARK: definition of well-formedness *)
Definition wellformed (e : expr) : Prop :=
  forall e' K, is_cf_expr e' -> e = fill' K e' -> scope_ctx' e K.


(** MARK: Regular Evaluation contexts *)
Inductive ectx :=
  | EmptyCtx
  | AppLCtx (K : ectx) (v2 : val)
  | AppRCtx (e1 : expr) (K : ectx)
  | UnOpCtx (op : un_op) (K : ectx)
  | BinOpLCtx (op : bin_op) (K : ectx) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr) (K : ectx)
  | IfCtx (K : ectx) (e1 e2 : expr)
  | PairLCtx (K : ectx) (v2 : val)
  | PairRCtx (e1 : expr) (K : ectx)
  | FstCtx (K : ectx)
  | SndCtx (K : ectx)
  | InjLCtx (K : ectx)
  | InjRCtx (K : ectx)
  | CaseCtx (K : ectx) (e1 : expr) (e2 : expr)
  | AllocNLCtx (K : ectx) (v2 : val)
  | AllocNRCtx (e1 : expr) (K : ectx)
  | LoadCtx (K : ectx)
  | StoreLCtx (K : ectx) (v2 : val)
  | StoreRCtx (e1 : expr) (K : ectx)
  | CmpXchgLCtx (K : ectx) (v1 : val) (v2 : val)
  | CmpXchgMCtx (e0 : expr) (K : ectx) (v2 : val)
  | CmpXchgRCtx (e0 : expr) (e1 : expr) (K : ectx)
  | FaaLCtx (K : ectx) (v2 : val)
  | FaaRCtx (e1 : expr) (K : ectx)
  (* TODO: possible problems with the resolve context *)
  (* | ResolveLCtx (K : ectx) (v1 : val) (v2 : val) *)
  (* | ResolveMCtx (e0 : expr) (K : ectx) (v2 : val) *)
  (* | ResolveRCtx (e0 : expr) (e1 : expr) (K : ectx) *)
  (* MARK: new contexts *)
  | LoopBCtx (eb : expr) (K : ectx)
  | BreakCtx (K : ectx)
  | CallCtx (K : ectx)
  | ReturnCtx (K : ectx).

Fixpoint comp_ectx (K1 K2 : ectx) : ectx :=
  match K1 with
  | EmptyCtx => K2
  | AppLCtx K v2 => AppLCtx (comp_ectx K K2) v2
  | AppRCtx e1 K => AppRCtx e1 (comp_ectx K K2)
  | UnOpCtx op K => UnOpCtx op (comp_ectx K K2)
  | BinOpLCtx op K v2 => BinOpLCtx op (comp_ectx K K2) v2
  | BinOpRCtx op e1 K => BinOpRCtx op e1 (comp_ectx K K2)
  | IfCtx K e1 e2 => IfCtx (comp_ectx K K2) e1 e2
  | PairLCtx K v2 => PairLCtx (comp_ectx K K2) v2
  | PairRCtx e1 K => PairRCtx e1 (comp_ectx K K2)
  | FstCtx K => FstCtx (comp_ectx K K2)
  | SndCtx K => SndCtx (comp_ectx K K2)
  | InjLCtx K => InjLCtx (comp_ectx K K2)
  | InjRCtx K => InjRCtx (comp_ectx K K2)
  | CaseCtx K e1 e2 => CaseCtx (comp_ectx K K2) e1 e2
  | AllocNLCtx K v2 => AllocNLCtx (comp_ectx K K2) v2
  | AllocNRCtx e1 K => AllocNRCtx e1 (comp_ectx K K2)
  | LoadCtx K => LoadCtx (comp_ectx K K2)
  | StoreLCtx K v2 => StoreLCtx (comp_ectx K K2) v2
  | StoreRCtx e1 K => StoreRCtx e1 (comp_ectx K K2)
  | CmpXchgLCtx K v1 v2 => CmpXchgLCtx (comp_ectx K K2) v1 v2
  | CmpXchgMCtx e0 K v2 => CmpXchgMCtx e0 (comp_ectx K K2) v2
  | CmpXchgRCtx e0 e1 K => CmpXchgRCtx e0 e1 (comp_ectx K K2)
  | FaaLCtx K v2 => FaaLCtx (comp_ectx K K2) v2
  | FaaRCtx e1 K => FaaRCtx e1 (comp_ectx K K2)
  (* TODO: possible problems with the resolve context *)
  (* | ResolveLCtx K v1 v2 => ResolveLCtx (comp_ectx K K2) v1 v2 *)
  (* | ResolveMCtx e0 K v2 => ResolveMCtx e0 (comp_ectx K K2) v2 *)
  (* | ResolveRCtx e0 e1 K => ResolveRCtx e0 e1 (comp_ectx K K2) *)
  (* MARK: new contexts *)
  | LoopBCtx eb K => LoopBCtx eb (comp_ectx K K2)
  | BreakCtx K => BreakCtx (comp_ectx K K2)
  | CallCtx K => CallCtx (comp_ectx K K2)
  | ReturnCtx K => ReturnCtx (comp_ectx K K2)
  end.

(* MARK: impenetrable contexts *)
Inductive impenetrable_ectx : expr -> ectx -> Prop :=
  | BreakImpenLoop e eb K:
    impenetrable_ectx (EBreak e) (LoopBCtx eb K)
  | BreakImpenCall e K:
    impenetrable_ectx (EBreak e) (CallCtx K)
  | ContinueImpenLoop eb K:
    impenetrable_ectx EContinue (LoopBCtx eb K)
  | ContinueImpenCall K:
    impenetrable_ectx EContinue (CallCtx K)
  | ReturnImpenCall e K:
    impenetrable_ectx (EReturn e) (CallCtx K)
  | CompImpenCtx e K K':
    ~ K' = EmptyCtx ->
    impenetrable_ectx e K ->
    impenetrable_ectx e (comp_ectx K' K).

(** Contextual closure will only reduce [e] in [Resolve e (Val _) (Val _)] if
the local context of [e] is non-empty. As a consequence, the first argument of
[Resolve] is not completely evaluated (down to a value) by contextual closure:
no head steps (i.e., surface reductions) are taken. This means that contextual
closure will reduce [Resolve (CmpXchg #l #n (#n + #1)) #p #v] into [Resolve
(CmpXchg #l #n #(n+1)) #p #v], but it cannot context-step any further. *)

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | EmptyCtx => e
  | AppLCtx K v2 => App (fill K e) (Val v2)
  | AppRCtx e1 K => App e1 (fill K e)
  | UnOpCtx op K => UnOp op (fill K e)
  | BinOpLCtx op K v2 => BinOp op (fill K e) (Val v2)
  | BinOpRCtx op e1 K => BinOp op e1 (fill K e)
  | IfCtx K e1 e2 => If (fill K e) e1 e2
  | PairLCtx K v2 => Pair (fill K e) (Val v2)
  | PairRCtx e1 K => Pair e1 (fill K e)
  | FstCtx K => Fst (fill K e)
  | SndCtx K => Snd (fill K e)
  | InjLCtx K => InjL (fill K e)
  | InjRCtx K => InjR (fill K e)
  | CaseCtx K e1 e2 => Case (fill K e) e1 e2
  | AllocNLCtx K v2 => AllocN (fill K e) (Val v2)
  | AllocNRCtx e1 K => AllocN e1 (fill K e)
  | LoadCtx K => Load (fill K e)
  | StoreLCtx K v2 => Store (fill K e) (Val v2)
  | StoreRCtx e1 K => Store e1 (fill K e)
  | CmpXchgLCtx K v1 v2 => CmpXchg (fill K e) (Val v1) (Val v2)
  | CmpXchgMCtx e0 K v2 => CmpXchg e0 (fill K e) (Val v2)
  | CmpXchgRCtx e0 e1 K => CmpXchg e0 e1 (fill K e)
  | FaaLCtx K v2 => FAA (fill K e) (Val v2)
  | FaaRCtx e1 K => FAA e1 (fill K e)
  (* | ResolveLCtx K v1 v2 => Resolve (fill K e) (Val v1) (Val v2) *)
  (* | ResolveMCtx ex K v2 => Resolve ex (fill K e) (Val v2) *)
  (* | ResolveRCtx ex e1 K => Resolve ex e1 (fill K e) *)
  (* MARK: new rules for new contexts *)
  | LoopBCtx eb K => LoopB eb (fill K e)
  | BreakCtx K => EBreak (fill K e)
  | CallCtx K => Call (fill K e)
  | ReturnCtx K => EReturn (fill K e)
  end.

(** Basic properties about the language *)
Instance fill_inj K : Inj (=) (=) (fill K).
Proof. induction K; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_sval K e :
  is_Some (to_sval (fill K e)) → is_Some (to_sval e).
Proof.
  intros [v ?]. revert H. revert v.
  induction K; inversion 1.
  - rewrite H1. eauto.
  - destruct (fill K e); inversion H1.
    apply IHK with (SVal v0). eauto.
  - destruct (fill K e); inversion H1.
    apply IHK with (SVal v0). eauto.
Qed.

Lemma fill_val K e :
  is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  intros [v ?]. revert H. revert v.
  induction K; inversion 1.
  rewrite H1. eauto.
Qed.

Lemma fill_not_sval K e:
  to_sval e = None → to_sval (fill K e) = None.
Proof.
  intros.
  assert (~(is_Some (to_sval e))). {
    unfold not. rewrite H. apply is_Some_None.
  }
  assert (~(is_Some (to_sval (fill K e)))). {
    unfold not in *. intros. apply fill_sval in H1. auto.
  }
  unfold not in H1.
  destruct (to_sval (fill K e)); auto.
  exfalso. apply H1. eauto.
Qed.

Lemma fill_not_val K e:
  to_val e = None → to_val (fill K e) = None.
Proof.
  intros.
  assert (~(is_Some (to_val e))). {
    unfold not. rewrite H. apply is_Some_None.
  }
  assert (~(is_Some (to_val (fill K e)))). {
    unfold not in *. intros. apply fill_val in H1. auto.
  }
  unfold not in H1.
  destruct (to_val (fill K e)); auto.
  exfalso. apply H1. eauto.
Qed.

Ltac destruct_inversion K H :=
destruct K; simpl in H; inversion H; subst.


Module expr_depth.
Import Omega.
Open Scope nat_scope.

Fixpoint expr_depth (e : expr) : nat :=
  match e with
  | Val _ | Var _ | Rec _ _ _
  (* | NewProph  *)
  | EContinue => 1
  | App e1 e2 | Pair e1 e2
  | BinOp _ e1 e2 | AllocN e1 e2
  | Store e1 e2 | FAA e1 e2
    => match (to_val e2) with
       | Some _ => 1 + expr_depth e1
       | None  => 1 + expr_depth e2
       end
  | UnOp _ e | If e _ _
  | Fst e | Snd e
  | InjL e | InjR e
  | Case e _ _ | Fork e
  | Load e | LoopB _ e
  | EBreak e | Call e
  | EReturn e
    => 1 + expr_depth e
  | CmpXchg e0 e1 e2
  (* | Resolve e0 e1 e2 *)
    => match (to_val e1), (to_val e2) with
       | _, None => 1 + expr_depth e2
       | None, Some _ => 1 + expr_depth e1
       | Some _, Some _ => 1 + expr_depth e0
       end
  end.

Fixpoint ectx_depth (K : ectx) : nat :=
  match K with
  | EmptyCtx => 0 
  | AppLCtx K _ | AppRCtx _ K
  | UnOpCtx _ K | BinOpLCtx _ K _
  | BinOpRCtx _ _ K | IfCtx K _ _
  | PairLCtx K _ | PairRCtx _ K
  | FstCtx K | SndCtx K
  | InjLCtx K | InjRCtx K
  | CaseCtx K _ _ | AllocNLCtx K _
  | AllocNRCtx _ K | LoadCtx K
  | StoreLCtx K _ | StoreRCtx _ K
  | CmpXchgLCtx K _ _ | CmpXchgMCtx _ K _
  | CmpXchgRCtx _ _ K | FaaLCtx K _
  | FaaRCtx _ K
  (* | ResolveLCtx K _ _ | ResolveMCtx _ K _ | ResolveRCtx _ _ K *)
  | LoopBCtx _ K | BreakCtx K
  | CallCtx K | ReturnCtx K
    => 1 + ectx_depth K
  end.

Lemma fill_depth K e :
  to_val e = None ->
  expr_depth (fill K e) = (ectx_depth K) + (expr_depth e).
Proof.
  intros.
  (* pose proof fill_not_val K _ H. *)
  induction K; simpl in *; eauto;
  try (pose proof fill_not_val K _ H; rewrite H0);
  try (rewrite IHK; try destruct (to_val e1); eauto).
Qed.

Definition singleton_ectx K : Prop := ectx_depth K = 1.
Definition singleton_expr e : Prop := expr_depth e = 1.

Close Scope nat_scope.
End expr_depth.
Import expr_depth.


(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
  | Fork e => Fork (subst x v e)
  | AllocN e1 e2 => AllocN (subst x v e1) (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | CmpXchg e0 e1 e2 => CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
  | FAA e1 e2 => FAA (subst x v e1) (subst x v e2)
  (* | NewProph => NewProph *)
  (* | Resolve ex e1 e2 => Resolve (subst x v ex) (subst x v e1) (subst x v e2) *)
  (* MARK: new rules for new expressions *)
  | LoopB eb e => LoopB (subst x v eb) (subst x v e)  (* TODO: not sure wether to subst eb *)
  | EBreak e => EBreak (subst x v e)
  | EContinue => EContinue
  | Call e => Call (subst x v e)
  | EReturn e => EReturn (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | QuotOp => Some $ LitInt (n1 `quot` n2)
  | RemOp => Some $ LitInt (n1 `rem` n2)
  | AndOp => Some $ LitInt (Z.land n1 n2)
  | OrOp => Some $ LitInt (Z.lor n1 n2)
  | XorOp => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp => Some $ LitInt (n1 ≪ n2)
  | ShiftROp => Some $ LitInt (n1 ≫ n2)
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  | OffsetOp => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | _, _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    (* Crucially, this compares the same way as [CmpXchg]! *)
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.

Definition state_upd_heap (f: gmap loc val → gmap loc val) (σ: state) : state :=
  {| heap := f σ.(heap); used_proph_id := σ.(used_proph_id) |}.
Arguments state_upd_heap _ !_ /.

Definition state_upd_used_proph_id (f: gset proph_id → gset proph_id) (σ: state) : state :=
  {| heap := σ.(heap); used_proph_id := f σ.(used_proph_id) |}.
Arguments state_upd_used_proph_id _ !_ /.

Fixpoint heap_array (l : loc) (vs : list val) : gmap loc val :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l vs w k :
  heap_array l vs !! k = Some w ↔
  ∃ j, 0 ≤ j ∧ k = l +ₗ j ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ->] | (Hl & j & ? & -> & ?)].
    { exists 0. rewrite loc_add_0. naive_solver lia. }
    exists (1 + j). rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0; eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj _); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    exists (j - 1). rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc val) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i) → (i < length vs) → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&?&->&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_init_heap (l : loc) (n : Z) (v : val) (σ : state) : state :=
  state_upd_heap (λ h, heap_array l (replicate (Z.to_nat n) v) ∪ h) σ.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = state_upd_heap <[l:=v]> σ.
Proof.
  destruct σ as [h p]. rewrite /state_init_heap /=. f_equiv.
  rewrite right_id insert_union_singleton_l. done.
Qed.

Module NoContinue.
Fixpoint no_continue (e : expr) : Prop :=
  match e with
  | Var _ | Fork _ 
    => True
  | EContinue => False
  | App e1 e2 | Pair e1 e2
  | BinOp _ e1 e2 | AllocN e1 e2
  | Store e1 e2 | FAA e1 e2
  | LoopB e1 e2
    => no_continue e1 /\ no_continue e2
  | UnOp _ e 
  | Rec _ _ e
  | Fst e | Snd e
  | InjL e | InjR e
  | Load e | Call e 
  | EBreak e | EReturn e
    => no_continue e
  | If e0 e1 e2
  | Case e0 e1 e2
  | CmpXchg e0 e1 e2
    => no_continue e0 /\ no_continue e1 /\ no_continue e2
  | Val v => no_continue_val v
  end
with no_continue_val (v : val) : Prop :=
  match v with
  | RecV _ _ e => no_continue e
  | PairV v1 v2 => no_continue_val v1 /\ no_continue_val v2
  | InjLV v => no_continue_val v
  | InjRV v => no_continue_val v
  | _ => True 
end.

Lemma no_continue_un_op op v v':
  no_continue (Val v) ->
  un_op_eval op v = Some v' ->
  no_continue_val v'.
Proof.
  intros H. revert v'.
  induction v; intros; simpl in *.
  - destruct op, l; simpl in *;
    inversion H0; auto.
  - destruct op; inversion H0.
  - destruct op; inversion H0.
  - destruct op; inversion H0.
  - destruct op; inversion H0.
Qed.

Lemma no_continue_bin_op op v1 v2 v':
  no_continue (Val v1) ->
  no_continue (Val v2) ->
  bin_op_eval op v1 v2 = Some v' ->
  no_continue_val v'.    
Proof.
  intros.
  unfold bin_op_eval in H1.
  destruct (decide (op = EqOp)).
  - destruct (decide (vals_compare_safe v1 v2)); inversion H1.
    destruct (bool_decide (v1 = v2)); simpl; auto.
  - destruct v1; inversion H1; clear H1.
    destruct l; inversion H3; clear H3;
    destruct v2; inversion H2; clear H2;
    destruct l; inversion H3; clear H3.
    + destruct op; inversion H2; auto.
    + destruct op; inversion H2; auto.
    + destruct op; inversion H2.
      destruct l0; inversion H3.
      auto.
Qed.

Definition no_continue_state (σ : state) : Prop :=
  forall l v, heap σ !! l = Some v -> no_continue_val v.
End NoContinue.

Export NoContinue.

Inductive head_step : expr → state → list observation → expr → state → list expr → Prop :=
  (* Original ones *)
  | RecS f x e σ :
     head_step (Rec f x e) σ [] (Val $ RecV f x e) σ []
  | PairS v1 v2 σ :
     head_step (Pair (Val v1) (Val v2)) σ [] (Val $ PairV v1 v2) σ []
  | InjLS v σ :
     head_step (InjL $ Val v) σ [] (Val $ InjLV v) σ []
  | InjRS v σ :
     head_step (InjR $ Val v) σ [] (Val $ InjRV v) σ []
  | BetaS f x e1 v2 e' σ :
     e' = subst' x v2 (subst' f (RecV f x e1) e1) →
     head_step (App (Val $ RecV f x e1) (Val v2)) σ [] e' σ []
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     head_step (UnOp op (Val v)) σ [] (Val v') σ []
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     head_step (BinOp op (Val v1) (Val v2)) σ [] (Val v') σ []
  | IfTrueS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool true) e1 e2) σ [] e1 σ []
  | IfFalseS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool false) e1 e2) σ [] e2 σ []
  | FstS v1 v2 σ :
     head_step (Fst (Val $ PairV v1 v2)) σ [] (Val v1) σ []
  | SndS v1 v2 σ :
     head_step (Snd (Val $ PairV v1 v2)) σ [] (Val v2) σ []
  | CaseLS v e1 e2 σ :
     head_step (Case (Val $ InjLV v) e1 e2) σ [] (App e1 (Val v)) σ []
  | CaseRS v e1 e2 σ :
     head_step (Case (Val $ InjRV v) e1 e2) σ [] (App e2 (Val v)) σ []
  | ForkS e σ:
     wellformed e ->  (* MARK: The forked program must be wellformed *)
     head_step (Fork e) σ [] (Val $ LitV LitUnit) σ [e]
  | AllocNS n v σ l :
     (* MARK: *)
     no_continue_val v ->   
     0 < n →
     (∀ i, 0 ≤ i → i < n → σ.(heap) !! (l +ₗ i) = None) →
     head_step (AllocN (Val $ LitV $ LitInt n) (Val v)) σ
               []
               (Val $ LitV $ LitLoc l) (state_init_heap l n v σ)
               []
  | LoadS l v σ :
     σ.(heap) !! l = Some v →
     head_step (Load (Val $ LitV $ LitLoc l)) σ [] (Val v) σ []
  | StoreS l v σ :
     (* MARK: *)
     no_continue_val v ->
     is_Some (σ.(heap) !! l) →
     head_step (Store (Val $ LitV $ LitLoc l) (Val v)) σ
               []
               (Val $ LitV LitUnit) (state_upd_heap <[l:=v]> σ)
               []
  | CmpXchgS l v1 v2 vl σ b :
     (* MARK: *)
     no_continue_val v2 ->
     σ.(heap) !! l = Some vl →
     (* Crucially, this compares the same way as [EqOp]! *)
     vals_compare_safe vl v1 →
     b = bool_decide (vl = v1) →
     head_step (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
               []
               (Val $ PairV vl (LitV $ LitBool b)) (if b then state_upd_heap <[l:=v2]> σ else σ)
               []
  | FaaS l i1 i2 σ :
     σ.(heap) !! l = Some (LitV (LitInt i1)) →
     head_step (FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2)) σ
               []
               (Val $ LitV $ LitInt i1) (state_upd_heap <[l:=LitV (LitInt (i1 + i2))]>σ)
               []
  (* | NewProphS σ p :
     p ∉ σ.(used_proph_id) →
     head_step NewProph σ
               []
               (Val $ LitV $ LitProphecy p) (state_upd_used_proph_id ({[ p ]} ∪.) σ)
               []
  | ResolveS p v e σ w σ' κs ts :
     head_step e σ κs (Val v) σ' ts →
     head_step (Resolve e (Val $ LitV $ LitProphecy p) (Val w)) σ
               (κs ++ [(p, (v, w))]) (Val v) σ' ts *)
  (* MARK: new head reductions for new expressions *)
  | LoopBS eb σ v:
    head_step (LoopB eb (Val v)) σ [] (LoopB eb eb) σ []   
    (* head_step (LoopB eb (Val $ LitV LitUnit)) σ [] (LoopB eb eb)  σ [] *)
  | LoopBBreakS eb v σ:
     head_step (LoopB eb (EBreak $ Val v)) σ [] (Val v) σ []
  | LoopBContinueS eb σ:
     head_step (LoopB eb EContinue) σ [] (LoopB eb eb) σ []
  | CallValueS σ v:
     head_step (Call (Val v)) σ [] (Val v) σ []
  | CallReturnS v σ:
     head_step (Call (EReturn $ Val v)) σ [] (Val v) σ []
  (* MARK: a more general step relation substitues all control-flow-context-related steps *)
  | CFCtxS e K σ:
     is_cf_terminal e ->  (* already require parameters of control flow evaluate to values *)
     singleton_ectx K ->
     ~ impenetrable_ectx e K ->
     head_step (fill K e) σ [] e σ [].

Module NoContinueHeadPreserve.
Lemma no_continue_state_preserve_head e1 σ1 κ e2 σ2 efs:
  no_continue_state σ1 ->
  head_step e1 σ1 κ e2 σ2 efs ->
  no_continue_state σ2.
Proof.
  intros.
  induction H0; auto.
  - unfold no_continue_state in *.
    intros. simpl in H3.
    apply lookup_union_Some_raw in H3.
    destruct H3 as [? | [? ?]].
    + apply heap_array_lookup in H3 as [j [? [? ?]]].
      apply lookup_replicate_1 in H5 as [? ?].
      subst; auto.
    + apply H in H4. auto.
  - unfold no_continue_state in *.
    intros. simpl in H2.
    destruct (loc_eq_decision l l0); subst.
    + rewrite lookup_insert in H2.
      inversion H2; subst. auto.
    + rewrite (lookup_insert_ne _ _ _ _ n) in H2.
      apply H in H2; auto.
  - clear H3; destruct b; auto.
    unfold no_continue_state in *.
    intros. simpl in H2.
    destruct (loc_eq_decision l l0); subst.
    + rewrite lookup_insert in H3.
      inversion H3; subst. auto.
    + rewrite (lookup_insert_ne _ _ _ _ n) in H3.
      apply H in H3; auto.
  - unfold no_continue_state in *.
    intros. simpl in H1.
    destruct (loc_eq_decision l l0); subst.
    + rewrite lookup_insert in H1.
      inversion H1; subst.
      simpl; auto.
    + rewrite (lookup_insert_ne _ _ _ _ n) in H1.
      apply H in H1; auto.
Qed.

Lemma no_continue_subst x v e:
  no_continue_val v ->
  no_continue e ->
  no_continue (subst' x v e).
Proof.
  intros.
  unfold subst'.
  destruct x; auto.
  induction e; simpl in *; auto;
  try (split; try destruct H0 as [? [? ?]]; try destruct H0; auto).
  - destruct (decide (s = x)); auto.
  - destruct (decide ((BNamed s) ≠ f ∧ (BNamed s) ≠ x)); auto.
Qed.

Lemma no_continue_preserve_head e1 σ1 κ e2 σ2 efs :
  no_continue_state σ1 ->  
  head_step e1 σ1 κ e2 σ2 efs ->
  no_continue e1 -> no_continue e2.
Proof.
  intro HStateNoContinue.
  intros.
  destruct e1; intros; simpl in H0; try inversion H0;
  inversion H; subst; simpl; auto;
  try match goal with
  | H: head_step ?e1 _ _ ?e2 _ _, H1: fill ?K ?e2 = ?e1 |- ?P =>
    destruct_inversion K H1
  end;
  try match goal with
  | H: expr_depth.singleton_ectx _ |- ?P =>
    unfold expr_depth.singleton_ectx in H;
    inversion H;
    try match goal with
    | H: expr_depth.ectx_depth ?K = 0%nat |- ?P =>
      destruct_inversion K H; auto
    end
  end;
  (* try (destruct H2; simpl; auto); *)
  (* try (destruct H0; auto); *)
  try apply (no_continue_un_op _ _ _ H0 H8);
  try (destruct H0; apply (no_continue_bin_op _ _ _ _ H0 H3 H11)).
  - apply no_continue_subst; auto.
    apply no_continue_subst; auto.
  - destruct H2; auto.
  - destruct H2. auto.
  - destruct H0; auto.
  - destruct H0; auto.
  - destruct H0, H2; auto.
  - destruct H0, H2; auto.
  - apply HStateNoContinue in H2; auto.
  - apply HStateNoContinue in H7; auto.
  - simpl in H2; tauto.
  - simpl in H2; tauto.
Qed.
End NoContinueHeadPreserve.

Lemma sval_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_sval e1 = None.
Proof.
  destruct 1; try naive_solver; try (destruct K; naive_solver).
  destruct K; try congruence; try naive_solver.
  - unfold singleton_ectx in H0; naive_solver.
  - simpl; destruct (fill K e) eqn: HK; auto.
    destruct K; inversion HK.
    simpl in HK. rewrite HK in H.
    inversion H.
  - simpl; destruct (fill K e) eqn: HK; auto.
    destruct K; inversion HK.
    simpl in HK. rewrite HK in H.
    inversion H.
Qed.

(* Head Reduction only reduce the most primitive expression *)
(* Lemma head_ctx_step_sval K e σ1 κ e2 σ2 efs :
  head_step (fill K e) σ1 κ e2 σ2 efs → is_Some (to_sval e).
Proof. revert κ e2.
  induction Ki; inversion 1; subst; eauto.

induction Ki; inversion_clear 1; simplify_option_eq; eauto.
Abort. *)

Lemma fill_comp (K1 K2 : ectx) (e : expr) :
  fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. induction K1; simpl; try rewrite IHK1; eauto. Qed.


Inductive prim_step (e1 : expr) (σ1 : state) (κ : list observation)
      (e2 : expr) (σ2 : state) (efs : list expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    head_step e1' σ1 κ e2' σ2 efs → prim_step e1 σ1 κ e2 σ2 efs.

Lemma sval_prim_stuck e1 σ1 κ e2 σ2 efs : prim_step e1 σ1 κ e2 σ2 efs → to_sval e1 = None.
Proof.
  destruct 1; clear H0.
  apply sval_head_stuck in H1. subst.
  revert H1. revert e1'. clear e2'.
  induction K; intros; subst; eauto.
  - apply IHK in H1.
    simpl. destruct (fill K e1'); eauto.
    inversion H1.
  - apply IHK in H1.
    simpl. destruct (fill K e1'); eauto.
    inversion H1.
Qed.

Lemma val_prim_stuck e1 σ1 κ e2 σ2 efs : prim_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof.
  intros.
  apply sval_prim_stuck in H.
  destruct e1; simpl in *; eauto.
  inversion H.
Qed.

(* Not sure required or not *)
Lemma fill_step e1 σ1 κ e2 σ2 efs K:
  prim_step e1 σ1 κ e2 σ2 efs →
  prim_step (fill K e1) σ1 κ (fill K e2) σ2 efs.
Proof.
  intros.
  inversion_clear H; subst.
  repeat rewrite fill_comp.
  apply Ectx_step with (comp_ectx K K0) e1' e2'; auto.
Qed.

Lemma step_by_val K K' e1 e1' σ1 κ e2 σ2 efs :
  fill K e1 = fill K' e1' →
  to_sval e1 = None →
  head_step e1' σ1 κ e2 σ2 efs →
  ∃ K'', K' = comp_ectx K K''.
Proof.
  intros.
  revert K' H.
  induction K; simpl; intros; eauto;
  destruct_inversion K' H;
  try match goal with
  | H: fill ?K1 ?e1 = fill ?K2 ?e2 |- ?P => pose proof IHK _ H as [? ?]; subst; eauto
  | H0: Val _ = fill ?K ?e, H1: head_step ?e _ _ _ _ _ |- ?P =>
    destruct_inversion K H0; inversion H1; subst;
    match goal with
    | H0: fill ?K ?e = Val _, H1: is_cf_terminal ?e |- ?P =>
      destruct_inversion K H0; inversion H1
    end
  | H0: fill ?K ?e = Val _, H1: to_sval ?e = None |- ?P =>
    destruct_inversion K H0; inversion H1
  end;
  inversion H1; subst;
  try match goal with
  | H: Val _ = fill ?K ?e, H0: to_sval _ = None |- ?P =>
    destruct_inversion K H; inversion H0
  | H: fill ?K ?e = _, H0: singleton_ectx _ |- ?P =>
    destruct_inversion K H;
    unfold singleton_ectx in H0; simpl H0; inversion H0;
    destruct_inversion K0 H0;
    try match goal with
    | H: fill EmptyCtx _ = fill ?K _, H0: is_cf_terminal _,
      H1: to_sval _ = None |- ?P =>
      simpl in H; subst; destruct_inversion K H0; inversion H1;
      match goal with
      | H: Val _ = fill ?K _, H0: to_sval _ = None |- ?P =>
        destruct_inversion K H; inversion H0
      end
    end;
    try match goal with
    | H: fill EmptyCtx ?e = Val _, H0: is_cf_terminal ?e |- ?P =>
      simpl in H; subst; inversion H0
    end
  end;
  try match goal with
  | H: Val _ = fill ?K _, H0: to_sval _ = None |- ?P =>
    destruct_inversion K H; inversion H0
  | H: _ = fill ?K _, H0: to_sval _ = None |- ?P =>
    destruct_inversion K H; inversion H0;
    match goal with
    | H: Val _ = fill ?K _ |- ?P =>
      destruct_inversion K H; inversion H0
    end
  end.
Qed.

Lemma fill_step_inv K e1 σ1 κ e2 σ2 efs :
  to_sval e1 = None → prim_step (fill K e1) σ1 κ e2 σ2 efs →
  ∃ e3, e2 = fill K e3 ∧ prim_step e1 σ1 κ e3 σ2 efs.
Proof.
  intros Hnval [K'' e1'' e2'' Heq1 -> Hstep].
  destruct (step_by_val K K'' e1 e1'' σ1 κ e2'' σ2 efs) as [K' ->]; eauto.
  rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
  exists (fill K' e2''); rewrite -fill_comp; split; auto; subst.
  apply Ectx_step with K' e1'' e2''; auto.
Qed.

(* Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. revert Ki1. induction Ki2, Ki1; naive_solver eauto with f_equal. Qed. *)

Lemma alloc_fresh v n σ :
  (* MARK: *)
  no_continue_val v ->
  let l := fresh_locs (dom (gset loc) σ.(heap)) in
  0 < n →
  head_step (AllocN ((Val $ LitV $ LitInt $ n)) (Val v)) σ []
            (Val $ LitV $ LitLoc l) (state_init_heap l n v σ) [].
Proof.
  intros.
  apply AllocNS; auto.
  intros. apply (not_elem_of_dom (D := gset loc)).
  by apply fresh_locs_fresh.
Qed.

(* Lemma new_proph_id_fresh σ :
  let p := fresh σ.(used_proph_id) in
  head_step NewProph σ [] (Val $ LitV $ LitProphecy p) (state_upd_used_proph_id ({[ p ]} ∪.) σ) [].
Proof. constructor. apply is_fresh. Qed. *)

Lemma cf_lang_mixin : LanguageMixin of_sval to_sval prim_step.
Proof.
  split; apply _ || eauto using to_of_sval, of_to_sval, sval_prim_stuck.
Qed.

Lemma aux_lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_prim_stuck.
Qed.
End cf_lang.

(** Language *)
Canonical Structure cf_lang := Language cf_lang.cf_lang_mixin.

(* Prefer cf_lang names over ectx_language names. *)
Export cf_lang.

(* DONE: congruence/deterministic lemma is no longer needed
Lemma head_step_congruence e e1 e2 σ σ1 σ2 κ1 κ2 efs1 efs2:
  head_step e σ κ1 e1 σ1 efs1 ->
  head_step e σ κ2 e2 σ2 efs2 ->
  κ1 = κ2 /\ e1 = e2 /\ σ1 = σ2 /\ efs1 = efs2.
Proof.
Admitted.

Lemma prim_step_congruence e e1 e2 σ σ1 σ2 κ1 κ2 efs1 efs2:
  prim_step e σ κ1 e1 σ1 efs1 ->
  prim_step e σ κ2 e2 σ2 efs2 ->
  κ1 = κ2 /\ e1 = e2 /\ σ1 = σ2 /\ efs1 = efs2.
Proof.
Admitted. *)

Module fill_no_val_inj.
Import expr_depth.
Import Omega.
(* Canonical Structure aux_lang := Language aux_lang_mixin. *)

Lemma fill_no_val_inj e K1 K2:
  to_val e = None ->
  fill K1 e = fill K2 e → K1 = K2.
Proof.
  intros ?.
  revert K1.
  induction K2, K1; try (simpl in *; naive_solver eauto with f_equal);
  try (intros Hdep; apply (f_equal expr_depth) in Hdep; simpl in Hdep; rewrite (fill_depth _ _ H) in Hdep;
  try rewrite (fill_not_val K1 _ H) in Hdep; try rewrite (fill_not_val K2 _ H) in Hdep;
  omega);
  try (intros Hdep; apply (f_equal expr_depth) in Hdep; repeat rewrite (fill_depth _ _ H) in Hdep; simpl in Hdep;
  try rewrite (fill_not_val K1 _ H) in Hdep; try rewrite (fill_not_val K2 _ H) in Hdep;
  omega);
  try
  (simpl; inversion 1; subst;
  match goal with
  | HK: fill ?K ?e = Val ?v |- ?P => destruct_inversion K HK; inversion H
  | HK: Val ?v = fill ?K ?e |- ?P => destruct_inversion K HK; inversion H
  end).
Qed.
End fill_no_val_inj.
Import fill_no_val_inj.

Lemma comp_empty K:
  comp_ectx K EmptyCtx = K.
Proof.
  induction K; simpl; try rewrite IHK; eauto.
Qed.

Lemma comp_assoc K1 K2 K3:
  comp_ectx (comp_ectx K1 K2) K3 = comp_ectx K1 (comp_ectx K2 K3).
Proof.
  revert K2 K3.
  induction K1; intros; simpl; try rewrite comp_empty; try rewrite IHK1; eauto.
Qed.

Lemma comp_penetrable e K1 K2:
  ~ impenetrable_ectx e (comp_ectx K1 K2) ->
  ~ impenetrable_ectx e K1 /\ ~ impenetrable_ectx e K2.
Proof.
  intros.
  split; unfold not in *;
  intros; apply H; clear H.
  {
    induction H0; simpl;
    [constructor|constructor|constructor|constructor|constructor|].
    rewrite comp_assoc; constructor; auto.
  }
  {
    destruct K1; auto; try constructor; auto.
  }
Qed.

Lemma cf_step_congruence e1 K1 σ1 κ e2 σ2 efs:
  is_cf_terminal e1 ->
  ¬ impenetrable_ectx e1 K1 ->
  head_step (fill K1 e1) σ1 κ e2 σ2 efs ->
  e1 = e2 ∧ σ1 = σ2 ∧ κ = [] ∧ efs = [].
Proof.
  intros.
  remember (fill K1 e1) as e1'.
  revert K1 Heqe1' H0.
  destruct H;
  induction H1; intros; subst;
  match goal with
  | _: is_cf_terminal ?e1 |- ?P => idtac
  | |- ?P =>
    (destruct_inversion K1 Heqe1';
    try
    match goal with
    | HK: Val _ = fill ?K _ |- ?P => destruct_inversion K HK
    end;
    try
    match goal with
    | Hpen: ~ impenetrable_ectx _ _ |- ?P => exfalso; apply Hpen; constructor
    end)
  end.
  (* - assert (fill K1 (EBreak (Val v)) = fill K1 (EBreak (Val v))); auto.
    replace (ResolveLCtx K1 (LitV (LitProphecy p)) v2) with (comp_ectx (ResolveLCtx EmptyCtx (LitV (LitProphecy p)) v2) K1) in H0; auto.
    apply comp_penetrable in H0 as [_ ?].
    pose proof IHhead_step K1 H H0 as [? _].
    inversion H2. *)
  - clear H0 H1 H2.
    repeat split; auto.
    destruct H;
    [repeat f_equal | exfalso | exfalso];
    revert K1 Heqe1';
    induction K; intros; simpl in *; destruct_inversion K1 Heqe1'; auto;
    try
    match goal with
    | H: fill _ _ = fill _ _ |- ?P => apply IHK in H; auto
    end;
    try
    match goal with
    | H: Val _ = fill ?K _ |- ?P => destruct_inversion K H
    | H: fill ?K _ = Val _ |- ?P => destruct_inversion K H
    end.
  (* - assert (fill K1 EContinue = fill K1 EContinue); auto.
    replace (ResolveLCtx K1 (LitV (LitProphecy p)) v2) with (comp_ectx (ResolveLCtx EmptyCtx (LitV (LitProphecy p)) v2) K1) in H0; auto.
    apply comp_penetrable in H0 as [_ ?].
    pose proof IHhead_step K1 H H0 as [? _].
    inversion H2. *)
  - clear H0 H1 H2.
    repeat split; auto.
    destruct H;
    [exfalso | repeat f_equal | exfalso];
    revert K1 Heqe1';
    induction K; intros; simpl in *; destruct_inversion K1 Heqe1'; auto;
    try
    match goal with
    | H: fill _ _ = fill _ _ |- ?P => apply IHK in H; auto
    end;
    try
    match goal with
    | H: Val _ = fill ?K _ |- ?P => destruct_inversion K H
    | H: fill ?K _ = Val _ |- ?P => destruct_inversion K H
    end.
  (* - assert (fill K1 (EReturn (Val v)) = fill K1 (EReturn (Val v))); auto.
    replace (ResolveLCtx K1 (LitV (LitProphecy p)) v2) with (comp_ectx (ResolveLCtx EmptyCtx (LitV (LitProphecy p)) v2) K1) in H0; auto.
    apply comp_penetrable in H0 as [_ ?].
    pose proof IHhead_step K1 H H0 as [? _].
    inversion H2. *)
  - destruct_inversion K1 H2.
    destruct_inversion K1 H1.
  - destruct_inversion K1 H2.
  - clear H0 H1 H2.
    repeat split; auto.
    destruct H;
    [exfalso | exfalso | repeat f_equal];
    revert K1 Heqe1';
    induction K; intros; simpl in *; destruct_inversion K1 Heqe1'; auto;
    try
    match goal with
    | H: fill _ _ = fill _ _ |- ?P => apply IHK in H; auto
    end;
    try
    match goal with
    | H: Val _ = fill ?K _ |- ?P => destruct_inversion K H
    | H: fill ?K _ = Val _ |- ?P => destruct_inversion K H
    end.
Qed.

Lemma fill_cf_inv e1 e2 K1 K2:
  is_cf_terminal e1 ->
  fill K1 e1 = fill K2 e2 ->
  (∃ v : val, e2 = Val v) ∨ (∃ K3 : ectx, e2 = fill K3 e1).
Proof.
  intros H.
  revert K2.
  destruct H;
  induction K1; intros; simpl in *;
  destruct_inversion K2 H;
  try apply IHK1 in H0;
  try apply IHK1 in H1;
  try apply IHK1 in H2;
  try apply IHK1 in H3;
  auto;
  try 
  match goal with
  | HK: Val ?v = fill ?K ?e |- ?P => left; destruct_inversion K HK; eauto
  | HK: fill ?K ?e = Val ?v |- ?P => left; destruct_inversion K HK; eauto
  end.
  - right; exists EmptyCtx; eauto.
  - right; exists (AppLCtx K1 v2); eauto.
  - right; exists (AppRCtx e1 K1); eauto.
  - right; exists (UnOpCtx op K1); eauto.
  - right; exists (BinOpLCtx op K1 v2); eauto.
  - right; exists (BinOpRCtx op e1 K1); eauto.
  - right; exists (IfCtx K1 e1 e0); eauto.
  - right; exists (PairLCtx K1 v2); eauto.
  - right; exists (PairRCtx e1 K1); eauto.
  - right; exists (FstCtx K1); eauto.
  - right; exists (SndCtx K1); eauto.
  - right; exists (InjLCtx K1); eauto.
  - right; exists (InjRCtx K1); eauto.
  - right; exists (CaseCtx K1 e1 e0); eauto.
  - right; exists (AllocNLCtx K1 v2); eauto.
  - right; exists (AllocNRCtx e1 K1); eauto.
  - right; exists (LoadCtx K1); eauto.
  - right; exists (StoreLCtx K1 v2); eauto.
  - right; exists (StoreRCtx e1 K1); eauto.
  - right; exists (CmpXchgLCtx K1 v1 v2); eauto.
  - right; exists (CmpXchgMCtx e0 K1 v2); eauto.
  - right; exists (CmpXchgRCtx e0 e1 K1); eauto.
  - right; exists (FaaLCtx K1 v2); eauto.
  - right; exists (FaaRCtx e1 K1); eauto.
  (* - right; exists (ResolveLCtx K1 v1 v2); eauto. *)
  (* - right; exists (ResolveMCtx e0 K1 v2); eauto. *)
  (* - right; exists (ResolveRCtx e0 e1 K1); eauto. *)
  - right; exists (LoopBCtx eb K1); eauto.
  - right; exists (BreakCtx K1); eauto.
  - right; exists (CallCtx K1); eauto.
  - right; exists (ReturnCtx K1); eauto.
  
  - right; exists EmptyCtx; eauto.
  - right; exists (AppLCtx K1 v2); eauto.
  - right; exists (AppRCtx e1 K1); eauto.
  - right; exists (UnOpCtx op K1); eauto.
  - right; exists (BinOpLCtx op K1 v2); eauto.
  - right; exists (BinOpRCtx op e1 K1); eauto.
  - right; exists (IfCtx K1 e1 e0); eauto.
  - right; exists (PairLCtx K1 v2); eauto.
  - right; exists (PairRCtx e1 K1); eauto.
  - right; exists (FstCtx K1); eauto.
  - right; exists (SndCtx K1); eauto.
  - right; exists (InjLCtx K1); eauto.
  - right; exists (InjRCtx K1); eauto.
  - right; exists (CaseCtx K1 e1 e0); eauto.
  - right; exists (AllocNLCtx K1 v2); eauto.
  - right; exists (AllocNRCtx e1 K1); eauto.
  - right; exists (LoadCtx K1); eauto.
  - right; exists (StoreLCtx K1 v2); eauto.
  - right; exists (StoreRCtx e1 K1); eauto.
  - right; exists (CmpXchgLCtx K1 v1 v2); eauto.
  - right; exists (CmpXchgMCtx e0 K1 v2); eauto.
  - right; exists (CmpXchgRCtx e0 e1 K1); eauto.
  - right; exists (FaaLCtx K1 v2); eauto.
  - right; exists (FaaRCtx e1 K1); eauto.
  (* - right; exists (ResolveLCtx K1 v1 v2); eauto. *)
  (* - right; exists (ResolveMCtx e0 K1 v2); eauto. *)
  (* - right; exists (ResolveRCtx e0 e1 K1); eauto. *)
  - right; exists (LoopBCtx eb K1); eauto.
  - right; exists (BreakCtx K1); eauto.
  - right; exists (CallCtx K1); eauto.
  - right; exists (ReturnCtx K1); eauto.
  
  - right; exists EmptyCtx; eauto.
  - right; exists (AppLCtx K1 v2); eauto.
  - right; exists (AppRCtx e1 K1); eauto.
  - right; exists (UnOpCtx op K1); eauto.
  - right; exists (BinOpLCtx op K1 v2); eauto.
  - right; exists (BinOpRCtx op e1 K1); eauto.
  - right; exists (IfCtx K1 e1 e0); eauto.
  - right; exists (PairLCtx K1 v2); eauto.
  - right; exists (PairRCtx e1 K1); eauto.
  - right; exists (FstCtx K1); eauto.
  - right; exists (SndCtx K1); eauto.
  - right; exists (InjLCtx K1); eauto.
  - right; exists (InjRCtx K1); eauto.
  - right; exists (CaseCtx K1 e1 e0); eauto.
  - right; exists (AllocNLCtx K1 v2); eauto.
  - right; exists (AllocNRCtx e1 K1); eauto.
  - right; exists (LoadCtx K1); eauto.
  - right; exists (StoreLCtx K1 v2); eauto.
  - right; exists (StoreRCtx e1 K1); eauto.
  - right; exists (CmpXchgLCtx K1 v1 v2); eauto.
  - right; exists (CmpXchgMCtx e0 K1 v2); eauto.
  - right; exists (CmpXchgRCtx e0 e1 K1); eauto.
  - right; exists (FaaLCtx K1 v2); eauto.
  - right; exists (FaaRCtx e1 K1); eauto.
  (* - right; exists (ResolveLCtx K1 v1 v2); eauto. *)
  (* - right; exists (ResolveMCtx e0 K1 v2); eauto. *)
  (* - right; exists (ResolveRCtx e0 e1 K1); eauto. *)
  - right; exists (LoopBCtx eb K1); eauto.
  - right; exists (BreakCtx K1); eauto.
  - right; exists (CallCtx K1); eauto.
  - right; exists (ReturnCtx K1); eauto.
Qed.


Lemma break_penetrable_preservation v K σ1 κ e2 σ2 efs:
  ¬ impenetrable_ectx (EBreak $ Val v) K ->
  prim_step (fill K (EBreak $ Val v)) σ1 κ e2 σ2 efs ->
  σ1 = σ2 /\ κ = [] /\ efs = [] /\
  exists K', e2 = fill K' (EBreak $ Val v) /\ ¬ impenetrable_ectx (EBreak $ Val v) K'.
Proof.
  intros.
  inversion H0; subst.

  pose proof fill_cf_inv _ _ _ _ (break_is_cft _) H1 as [[v' ?] | [K1 ?]]; subst;
  [inversion H3; subst; destruct_inversion K1 H2; inversion H5 |].

  rewrite fill_comp in H1.

  apply fill_no_val_inj in H1; auto; subst.
  
  apply comp_penetrable in H as [? ?].

  pose proof cf_step_congruence _ _ _ _ _ _ _ (break_is_cft _) H1 H3 as [? [? [? ?]]]; subst.
  repeat split; auto.
  exists K0.
  split; auto.
Qed.

Lemma continue_penetrable_preservation K σ1 κ e2 σ2 efs:
  ¬ impenetrable_ectx EContinue K ->
  prim_step (fill K EContinue) σ1 κ e2 σ2 efs ->
  σ1 = σ2 /\ κ = [] /\ efs = [] /\
  exists K', e2 = fill K' EContinue /\ ¬ impenetrable_ectx EContinue K'.
Proof.
  intros.
  inversion H0; subst.

  pose proof fill_cf_inv _ _ _ _ continue_is_cft H1 as [[v' ?] | [K1 ?]]; subst;
  [inversion H3; subst; destruct_inversion K1 H2; inversion H5 |].

  rewrite fill_comp in H1.

  apply fill_no_val_inj in H1; auto; subst.
  
  apply comp_penetrable in H as [? ?].

  pose proof cf_step_congruence _ _ _ _ _ _ _ continue_is_cft H1 H3 as [? [? [? ?]]]; subst.
  repeat split; auto.
  exists K0.
  split; auto.
Qed.

Lemma return_penetrable_preservation v K σ1 κ e2 σ2 efs:
  ¬ impenetrable_ectx (EReturn $ Val v) K ->
  prim_step (fill K (EReturn $ Val v)) σ1 κ e2 σ2 efs ->
  σ1 = σ2 /\ κ = [] /\ efs = [] /\
  exists K', e2 = fill K' (EReturn $ Val v) /\ ¬ impenetrable_ectx (EReturn $ Val v) K'.
Proof.
  intros.
  inversion H0; subst.

  pose proof fill_cf_inv _ _ _ _ (return_is_cft _) H1 as [[v' ?] | [K1 ?]]; subst;
  [inversion H3; subst; destruct_inversion K1 H2; inversion H5 |].

  rewrite fill_comp in H1.

  apply fill_no_val_inj in H1; auto; subst.
  
  apply comp_penetrable in H as [? ?].

  pose proof cf_step_congruence _ _ _ _ _ _ _ (return_is_cft _) H1 H3 as [? [? [? ?]]]; subst.
  repeat split; auto.
  exists K0.
  split; auto.
Qed.

Lemma my_reducible_fill K e σ :
reducible e σ → reducible (fill K e) σ.
Proof. unfold reducible in *. naive_solver eauto using fill_step. Qed.



Definition outer (K : ectx) : ectx :=
  match K with
  | EmptyCtx => EmptyCtx
  | AppLCtx _ v2 => AppLCtx EmptyCtx v2
  | AppRCtx e1 _ => AppRCtx e1 EmptyCtx
  | UnOpCtx op _ => UnOpCtx op EmptyCtx
  | BinOpLCtx op _ v2 => BinOpLCtx op EmptyCtx v2
  | BinOpRCtx op e1 _ => BinOpRCtx op e1 EmptyCtx
  | IfCtx _ e1 e2 => IfCtx EmptyCtx e1 e2
  | PairLCtx _ v2 => PairLCtx EmptyCtx v2
  | PairRCtx e1 _ => PairRCtx e1 EmptyCtx
  | FstCtx _ => FstCtx EmptyCtx
  | SndCtx _ => SndCtx EmptyCtx
  | InjLCtx _ => InjLCtx EmptyCtx
  | InjRCtx _ => InjRCtx EmptyCtx
  | CaseCtx _ e1 e2 => CaseCtx EmptyCtx e1 e2
  | AllocNLCtx _ v2 => AllocNLCtx EmptyCtx v2
  | AllocNRCtx e1 _ => AllocNRCtx e1 EmptyCtx
  | LoadCtx _ => LoadCtx EmptyCtx
  | StoreLCtx _ v2 => StoreLCtx EmptyCtx v2
  | StoreRCtx e1 _ => StoreRCtx e1 EmptyCtx
  | CmpXchgLCtx _ v1 v2 => CmpXchgLCtx EmptyCtx v1 v2
  | CmpXchgMCtx e0 _ v2 => CmpXchgMCtx e0 EmptyCtx v2
  | CmpXchgRCtx e0 e1 _ => CmpXchgRCtx e0 e1 EmptyCtx
  | FaaLCtx _ v2 => FaaLCtx EmptyCtx v2
  | FaaRCtx e1 _ => FaaRCtx e1 EmptyCtx
  (* | ResolveLCtx _ v1 v2 => Resolve (fill _ e) (Val v1) (Val v2) *)
  (* | ResolveMCtx ex _ v2 => Resolve ex (fill _ e) (Val v2) *)
  (* | ResolveRCtx ex e1 _ => Resolve ex e1 (fill _ e) *)
  (* MARK: new rules for new contexts *)
  | LoopBCtx eb _ => LoopBCtx eb EmptyCtx
  | BreakCtx _ => BreakCtx EmptyCtx
  | CallCtx _ => CallCtx EmptyCtx
  | ReturnCtx _ => ReturnCtx EmptyCtx
  end.

Definition inner (K : ectx) : ectx :=
  match K with
  | EmptyCtx => EmptyCtx
  | AppLCtx K _ | AppRCtx _ K
  | UnOpCtx _ K | BinOpLCtx _ K _
  | BinOpRCtx _ _ K | IfCtx K _ _
  | PairLCtx K _ | PairRCtx _ K
  | FstCtx K | SndCtx K
  | InjLCtx K | InjRCtx K
  | CaseCtx K _ _ | AllocNLCtx K _
  | AllocNRCtx _ K | LoadCtx K
  | StoreLCtx K _ | StoreRCtx _ K
  | CmpXchgLCtx K _ _ | CmpXchgMCtx _ K _
  | CmpXchgRCtx _ _ K | FaaLCtx K _
  | FaaRCtx _ K
  | LoopBCtx _ K | BreakCtx K
  | CallCtx K | ReturnCtx K
    => K
  end.

(* TODO: move to lang.v *)
Lemma cf_reducible: forall e K σ,
  is_cf_terminal e ->
  ¬ impenetrable_ectx e K ->
  to_sval (fill K e) = None ->
  reducible (fill K e) σ.
Proof.
  intros.
  destruct H;
  induction K; simpl in H1; inversion H1;
  match goal with
  | IHK: _ -> _ -> reducible (fill ?K'' _) _ |- reducible (fill ?K' ?e) ?σ =>
    match K' with
    (* | LoopBCtx _ _ => idtac *)
    | CallCtx _ =>
      match e with
      | EReturn _ => idtac
      | _ => exfalso; apply H0; constructor
      end
    | _ =>
      match goal with | |- reducible (fill ?K' _) _ =>
        destruct (to_sval (fill K'' e)) eqn:eq; 
        [
          destruct K''; simpl in eq; inversion eq;
          match K' with
          | BreakCtx _ => 
          pose K''; (* FIXME: why pose K'' *)
          try destruct_inversion K'' H3
          | ReturnCtx _ =>
          pose K''; (* FIXME: why pose K'' *)
          try destruct_inversion K'' H3
          | LoopBCtx ?eb ?K0 => 
            try destruct_inversion K'' H2;
            let e' :=
              match e with
              | EReturn _ => e | EBreak e => e
              (* | EContinue => (LoopB eb eb) *)
              end in
              exists nil, e', σ, nil; simpl;
              apply Ectx_step with EmptyCtx (fill (LoopBCtx eb K0) e) e'; auto; constructor
          | _ =>
            match goal with | |- reducible (fill ?K' _) _ =>
              try destruct_inversion K'' H2;
              exists nil, e, σ, nil; pose K';
              apply Ectx_step with EmptyCtx (fill (outer K') e) e;
              auto; constructor; 
              unfold expr_depth.singleton_ectx; auto; constructor
            end
          end
        |
          (* exfalso; apply FF *)
          replace (fill K' e) with (fill (outer K') (fill (inner K') e));
          replace K' with (comp_ectx (outer K') (inner K')) in H0; auto;
          apply comp_penetrable in H0 as [_ ?];
          apply my_reducible_fill; auto
        ]
      end
    end
  end.

  destruct (to_sval (fill K (EReturn $ Val v))) eqn:eq.
  - destruct K; simpl in eq; inversion eq.
    + exists nil, (Val v), σ, nil.
      apply Ectx_step with EmptyCtx (fill (CallCtx EmptyCtx) (EReturn $ Val v)) (Val v); auto.
      constructor.
    + destruct_inversion K H2.
    + destruct_inversion K H2.
  - replace (fill (CallCtx K) (EReturn $ Val v)) with (fill (CallCtx EmptyCtx) (fill K (EReturn $ Val v))); auto.
    replace (CallCtx K) with (comp_ectx (CallCtx EmptyCtx) K) in H0; auto.
    apply comp_penetrable in H0 as [_ ?]; auto.
    apply my_reducible_fill; auto.
Qed.

Lemma head_step_not_sval e1 σ1 κ e2 σ2 efs:
  head_step e1 σ1 κ e2 σ2 efs -> to_sval e1 = None.
Proof.
  inversion 1; subst; simpl in *; auto.
  destruct (to_sval (fill K e2)) eqn:eq; auto.
  destruct s; simpl in eq.
  + destruct_inversion (fill K e2) eq;
    [exfalso | destruct_inversion e eq | destruct_inversion e eq].
    inversion H; subst; simpl in *.
    destruct_inversion K0 H3. inversion H4.
  + destruct_inversion (fill K e2) eq; destruct_inversion e eq.
    inversion H; subst; simpl in *.
    unfold expr_depth.singleton_ectx in H6.
    destruct_inversion K0 H3; simpl in *; try congruence.
    destruct_inversion K0 H9. inversion H5.
  + destruct_inversion (fill K e2) eq;
    [destruct_inversion e eq | | destruct_inversion e eq].
    inversion H; subst; simpl in *.
    unfold expr_depth.singleton_ectx in H5.
    destruct_inversion K0 H3; simpl in *; try congruence.
  + destruct_inversion (fill K e2) eq; destruct_inversion e eq.
    inversion H; subst; simpl in *.
    unfold expr_depth.singleton_ectx in H6.
    destruct_inversion K0 H3; simpl in *; try congruence.
    destruct_inversion K0 H9. inversion H5.
Qed.

Ltac sval_head_step_inv H :=
    apply head_step_not_sval in H; inversion H.

Lemma reducible_not_sval e σ:
  reducible e σ -> to_sval e = None.
Proof.
  intros.
  destruct (to_sval e) eqn:eq; [exfalso | auto].
  destruct s, e; inversion eq; try (destruct e; inversion H1).
  + destruct H as (? & ? & ? & ? & H).
    inversion H.
    destruct_inversion K H0.
    sval_head_step_inv H3.
  + destruct H as (? & ? & ? & ? & H).
    inversion H.
    destruct_inversion K H0.
    - sval_head_step_inv H4.
    - destruct_inversion K H6.
      sval_head_step_inv H4.
  + destruct H as (? & ? & ? & ? & H).
    inversion H.
    destruct_inversion K H0.
    sval_head_step_inv H2.
  + destruct H as (? & ? & ? & ? & H).
    inversion H.
    destruct_inversion K H0.
    - sval_head_step_inv H4.
    - destruct_inversion K H6.
      sval_head_step_inv H4.
Qed.

(* (** The following lemma is not provable using the axioms of [ectxi_language].
The proof requires a case analysis over context items ([destruct i] on the
last line), which in all cases yields a non-value. To prove this lemma for
[ectxi_language] in general, we would require that a term of the form
[fill_item i e] is never a value. *)
Lemma to_val_fill_some K e v : to_val (fill K e) = Some v → K = [] ∧ e = Val v.
Proof.
  intro H. destruct K as [|Ki K]; first by apply of_to_val in H. exfalso.
  assert (to_val e ≠ None) as He.
  { intro A. by rewrite fill_not_val in H. }
  assert (∃ w, e = Val w) as [w ->].
  { destruct e; try done; eauto. }
  assert (to_val (fill (Ki :: K) (Val w)) = None).
  { destruct Ki; simpl; apply fill_not_val; done. }
  by simplify_eq.
Qed.

Lemma prim_step_to_val_is_head_step e σ1 κs w σ2 efs :
  prim_step e σ1 κs (Val w) σ2 efs → head_step e σ1 κs (Val w) σ2 efs.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.

(** If [e1] makes a head step to a value under some state [σ1] then any head
 step from [e1] under any other state [σ1'] must necessarily be to a value. *)
Lemma head_step_to_val e1 σ1 κ e2 σ2 efs σ1' κ' e2' σ2' efs' :
  head_step e1 σ1 κ e2 σ2 efs →
  head_step e1 σ1' κ' e2' σ2' efs' → is_Some (to_val e2) → is_Some (to_val e2').
Proof. destruct 1; inversion 1; naive_solver. Qed.

Lemma irreducible_resolve e v1 v2 σ :
  irreducible e σ → irreducible (Resolve e (Val v1) (Val v2)) σ.
Proof.
  intros H κs ** [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind; simpl in Hfill.
  - subst e1'. inversion step. eapply H. by apply head_prim_step.
  - rewrite fill_app /= in Hfill.
    destruct K; (inversion Hfill; subst; clear Hfill; try
      match goal with | H : Val ?v = fill Ks ?e |- _ =>
        (assert (to_val (fill Ks e) = Some v) as HEq by rewrite -H //);
        apply to_val_fill_some in HEq; destruct HEq as [-> ->]; inversion step
      end).
    apply (H κs (fill_item K (foldl (flip fill_item) e2' Ks)) σ' efs).
    econstructor 1 with (K := Ks ++ [K]); last done; simpl; by rewrite fill_app.
Qed. *)
