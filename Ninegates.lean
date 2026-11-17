/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Basic
public import Ninegates.Meldable.ClosedForm
public import Ninegates.Meldable.SequentialMoving
public import Ninegates.Wait.Basic
public import Ninegates.Wait.TwoPair
public import Ninegates.Wait.Classes
public import Ninegates.Wait.Positive
public import Ninegates.Wait.Bounds
public import Ninegates.Wait.Sharpness
public import Ninegates.Wait.ClassSizes
public import Ninegates.Wait.PillarRemainder
public import Ninegates.Wait.RequiredOne
public import Ninegates.Wait.Reverse
public import Ninegates.Standard.Valid
public import Ninegates.Standard.Graph
public import Ninegates.Standard.Classes
public import Ninegates.Cardinality
public import Ninegates.Numerical.Taiwanese
public import Ninegates.Numerical.OrderOne
public import Ninegates.Minimal.LiveNext
public import Ninegates.Wait.Abundance
public import Ninegates.Wait.Add
public import Ninegates.Minimal.Maximum
public import Ninegates.Minimal.Double.Minimal
public import Ninegates.Minimal.Criterion
public import Ninegates.Minimal.Alternating.Size
public import Ninegates.Minimal.Alternating.Prefix
public import Ninegates.Minimal.Alternating.Full
public import Ninegates.Minimal.Alternating.Scan
public import Ninegates.Minimal.Alternating.Critical
public import Ninegates.Minimal.Alternating.Minimal
public import Ninegates.Examples
public import Ninegates.MovingExamples
public import Ninegates.GraphExamples
public import Ninegates.SplitExamples
public import Ninegates.BoundsExamples

/-!
# Structural formalization of the rewritten paper

The library starts from integer virtual hands, with independent order, meld
count, and copy bound. All definitions and proofs use the current API. The
previous implementation is archived on the `v2` branch.
-/
