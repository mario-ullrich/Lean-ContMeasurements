/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import ContMeasurements.Scheme
import ContMeasurements.SplitCover
import ContMeasurements.Halving
import ContMeasurements.BorsukUlam
import ContMeasurements.LowerBound

/-!
# Adaptive continuous measurements

How many measurements does one need to recover a vector of an `m`-dimensional space
to within a prescribed accuracy, if each measurement may be an arbitrary continuous
functional and may be chosen on the basis of the values observed so far?
-/
