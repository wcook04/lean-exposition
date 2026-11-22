/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.TableauConstraints
import PCP.Reduction.ThreeSATGraphEncoding

/-!
# Arithmetic indices for machine-tableau variables and constraints

Only the stack enumeration is supplied. It is fixed by the source machine.
All input-sized indexing uses explicit sums and products of natural intervals.
-/

namespace PCP.Machine.TableauIndex

open Turing TM2Locality TableauConstraints

variable {tm : FinTM2} {k : ℕ}

def unitCode : Unit ≃ Fin 1 := (Equiv.equivPUnit (Fin 1)).symm

def siteCode (eK : tm.K ≃ Fin k) (B : ℕ) : Site tm B ≃ Fin (1 + k * B) :=
  (Equiv.sumCongr unitCode
    ((Equiv.prodCongr eK (Equiv.refl (Fin B))).trans finProdFinEquiv)).trans finSumFinEquiv

def variableCode (eK : tm.K ≃ Fin k) (T B : ℕ) :
    Variable tm T B ≃ Fin ((T + 1) * (1 + k * B) + 1) :=
  (Equiv.sumCongr
    ((Equiv.prodCongr (Equiv.refl (Fin (T + 1))) (siteCode eK B)).trans finProdFinEquiv)
    unitCode).trans finSumFinEquiv

def linkCode (eK : tm.K ≃ Fin k) (T : ℕ) :
    (Fin (T + 1) × tm.K × Fin (machineWindow tm)) ≃
      Fin ((T + 1) * (k * machineWindow tm)) :=
  (Equiv.prodCongr (Equiv.refl (Fin (T + 1)))
    ((Equiv.prodCongr eK (Equiv.refl (Fin (machineWindow tm)))).trans finProdFinEquiv)).trans
    finProdFinEquiv

def cellCode (eK : tm.K ≃ Fin k) (T B : ℕ) :
    (Fin T × tm.K × Fin B) ≃ Fin (T * (k * B)) :=
  (Equiv.prodCongr (Equiv.refl (Fin T))
    ((Equiv.prodCongr eK (Equiv.refl (Fin B))).trans finProdFinEquiv)).trans finProdFinEquiv

def boundaryCode (eK : tm.K ≃ Fin k) (B : ℕ) :
    (Bool × Site tm B) ≃ Fin (2 * (1 + k * B)) :=
  (Equiv.prodCongr PCP.Reduction.ThreeSATGraphEncoding.boolCode (siteCode eK B)).trans
    finProdFinEquiv

def constraintCode (eK : tm.K ≃ Fin k) (T B : ℕ) : Constraint tm T B ≃
    Fin (1 + (T + 1) * (k * machineWindow tm) + T + T * (k * B) + 2 * (1 + k * B)) :=
  ((Equiv.sumCongr unitCode
    ((Equiv.sumCongr (linkCode eK T)
      ((Equiv.sumCongr (Equiv.refl (Fin T))
        ((Equiv.sumCongr (cellCode eK T B) (boundaryCode eK B)).trans finSumFinEquiv)).trans
          finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv).trans
            (finCongr (by omega))

/-- Extra unary or pairwise witness constraints append in their natural numeric order. -/
def withWitnessCode (eK : tm.K ≃ Fin k) (T B W : ℕ) :
    (Constraint tm T B ⊕ Fin W) ≃
      Fin (1 + (T + 1) * (k * machineWindow tm) + T + T * (k * B) +
        2 * (1 + k * B) + W) :=
  (Equiv.sumCongr (constraintCode eK T B) (Equiv.refl (Fin W))).trans finSumFinEquiv

end PCP.Machine.TableauIndex
