datatype Problem = Problem(n: int, c: int, gains: seq<int>, weights: seq<int>)

type Solution = seq<int> 

function gain(p: Problem, solution: Solution): int
  requires isValidProblem(p)
  requires hasAllowedValues(solution)
  requires 0 <= |solution| <= p.n
{
  if |solution| == 0 then 0 else computeGain(p, solution, |solution| - 1)
}

function computeGain(p: Problem, solution: Solution, i: int) : int
  requires isValidProblem(p)
  requires 0 <= i < |solution|
  requires 0 <= i < |p.gains|
  requires hasAllowedValues(solution)
  requires 0 <= |solution| <= |p.gains|

  ensures computeGain(p, solution, i) >= 0
{
  if i == 0 then solution[0] * p.gains[0] else solution[i] * p.gains[i] + computeGain(p, solution, i - 1)
}

function weight(p: Problem, solution: Solution): int
  requires isValidProblem(p)
  requires hasAllowedValues(solution)
  requires 0 <= |solution| <= p.n
{
  if |solution| == 0 then 0 else computeWeight(p, solution, |solution| - 1)
}

function computeWeight(p: Problem, solution: Solution, i: int) : int
  requires forall i :: 0 <= i < |p.weights| ==> p.weights[i] > 0 
  requires 0 <= i < |solution|
  requires 0 <= i < |p.weights|
  requires hasAllowedValues(solution)
  requires 0 <= |solution| <= |p.weights|
  
  ensures computeWeight(p, solution, i) >= 0
{
  if i == 0 then solution[0] * p.weights[0] else solution[i] * p.weights[i] + computeWeight(p, solution, i - 1)
}

function sumAllGains(p: Problem, i: int) : int
 requires isValidProblem(p)
 requires 1 <= i <= p.n

 ensures sumAllGains(p, i) >= 0
{
  if (i == 1) then p.gains[0] else p.gains[i - 1] + sumAllGains(p, i -1)
}

predicate hasPositiveValues(solution: Solution)
{
  forall i :: 0 <= i < |solution| ==> solution[i] > 0
}

predicate hasAllowedValues(solution: Solution)
{
  forall k :: 0 <= k < |solution| ==> solution[k] == 0 || solution[k] == 1
}

predicate isValidProblem(p: Problem)
{
  |p.gains| == |p.weights| == p.n && 
  p.n > 0 && p.c >= 0 && 
  hasPositiveValues(p.gains) && hasPositiveValues(p.weights) 
}

predicate isValidPartialSolution(p: Problem, solution: Solution)
  requires isValidProblem(p)
{
  hasAllowedValues(solution) && |solution| <= p.n
}

predicate isPartialSolution(p: Problem, solution: Solution, i: int, j: int)
  requires isValidProblem(p)
  requires 0 <= i <= p.n
  requires 0 <= j <= p.c
{
  isValidPartialSolution(p, solution) && |solution| == i &&
  weight(p, solution) <= j
}

predicate isSolution(p: Problem, solution: Solution)
  requires isValidProblem(p)
{
  isValidPartialSolution(p, solution) && |solution| == p.n &&
  weight(p, solution) <= p.c
}

ghost predicate isOptimalPartialSolution(p: Problem, solution: Solution, i: int, j: int)
  requires isValidProblem(p)
  requires 0 <= i <= p.n
  requires 0 <= j <= p.c
{
  isPartialSolution(p, solution, i, j) &&
  forall s: Solution :: (isPartialSolution(p, s, i, j) && |s| == |solution| 
      ==> gain(p, solution) >= gain(p, s))
}

ghost predicate isOptimalSolution(p: Problem, solution: Solution)
  requires isValidProblem(p)
  requires isValidPartialSolution(p, solution)
{
  isOptimalPartialSolution(p, solution, p.n, p.c) &&
  forall s: Solution :: (((isOptimalPartialSolution(p, s, p.n, p.c)) ==> 
  gain(p, solution) >= gain(p, s)))
}

predicate isValidSubproblem(p: Problem, i: int, j: int)
{
  isValidProblem(p) && 
  1 <= i <= p.n && 
  1 <= j <= p.c 
}

ghost predicate areValidSolutions(p: Problem, profits: seq<seq<int>>, solutions: seq<seq<seq<int>>>, i: int)
  requires isValidSubproblem(p, i, p.c)
{ 
  i == |profits| == |solutions| &&
  (forall k :: 0 <= k < i ==> |profits[k]| == |solutions[k]| == p.c + 1) && 
  (forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                    isOptimalPartialSolution(p, solutions[k][q], k, q)) && 
  (forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                gain(p, solutions[k][q]) == profits[k][q])
}

ghost predicate areValidPartialSolutions(p: Problem, profits: seq<seq<int>>, solutions: seq<seq<seq<int>>>, 
                partialProfits: seq<int>, partialSolutions: seq<seq<int>>, i: int, j: int) 
                
  requires isValidSubproblem(p, i, j)
{
  |partialSolutions| == |partialProfits| == j && 
  (forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolution(p, partialSolutions[k], i, k)) && 
  (forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k])
}

// lemma which proves that adding 1 to a solution it will not exceed capacity j
lemma computeWeightFits1(p: Problem, solution: Solution, i: int, j: int)
  requires isValidProblem(p)
  requires 0 <= |solution| < p.n
  requires hasAllowedValues(solution)
  requires 0 <= j <= p.c + 1
  requires i == |solution|
  requires weight(p, solution) <= j - p.weights[i]
  
  ensures computeWeight(p, solution + [1], |solution + [1]| - 1) <= j
{
  var s' := solution + [1];
  assert solution == s'[..|s'| - 1];

  for a := 0 to |s'[..|s'| - 1]|
    invariant 0 <= a <= |s'[..|s'| - 1]| + 1
    invariant forall k :: 0 <= k < a ==> computeWeight(p, solution, k) == computeWeight(p, s', k)
  { }
}

// lemma which proves that adding 0 to a solution will not exceed capacity j
lemma computeWeightFits0(p: Problem, solution: Solution, j: int)
  requires isValidProblem(p)
  requires hasAllowedValues(solution)
  requires 0 <= |solution| < p.n
  requires weight(p, solution) <= j
  
  ensures computeWeight(p, solution + [0], |solution + [0]| - 1) <= j 
{  
  if |solution| == 0 {
    assert weight(p, solution) <= j;
  } else {
    var s' := solution + [0];
    assert s'[..|s'| - 1] == solution;
    computeWeightAdd0(p, s', |s'| - 2);
    assert computeWeight(p, solution + [0], |solution + [0]| - 1) <= j;
  }
}

lemma computeWeightAdd0(p: Problem, solution: Solution, i: int)
  requires isValidProblem(p)
  requires hasAllowedValues(solution)
  requires 0 <= i < |solution| - 1
  requires 0 <= |solution| <= |p.weights|
  requires solution[|solution| - 1] == 0
  
  ensures computeWeight(p, solution, i) == computeWeight(p, solution[..|solution| - 1], i)
{ }

lemma weightAdd0(p: Problem, solution: Solution)
  requires isValidProblem(p)
  requires hasAllowedValues(solution)
  requires 0 < |solution| <= p.n
  requires solution[|solution| - 1] == 0
  
  ensures weight(p, solution) == weight(p, solution[..|solution| - 1])
{
  if |solution| == 1 {

  } else {
    assert computeWeight(p, solution, |solution| - 1) == computeWeight(p, solution, |solution| - 2);
    computeWeightAdd0(p, solution, |solution| - 2);
  }
}

lemma computeGainAdd0(p: Problem, solution: Solution, i: int)
  requires isValidProblem(p)
  requires hasAllowedValues(solution)
  requires 0 <= i < |solution| - 1
  requires 0 <= |solution| <= |p.gains|
  requires solution[|solution| - 1] == 0
  
  ensures computeGain(p, solution, i) == computeGain(p, solution[..|solution| - 1], i)
{ }

lemma gainAdd0(p: Problem, solution: Solution)
  requires isValidProblem(p)
  requires hasAllowedValues(solution)
  requires 0 < |solution| <= p.n
  requires solution[|solution| - 1] == 0
  
  ensures gain(p, solution) == gain(p, solution[..|solution| - 1])
{ 
  if |solution| == 1 {

  } else {
    assert computeGain(p, solution, |solution| - 1) == computeGain(p, solution, |solution| - 2);
    computeGainAdd0(p, solution, |solution| - 2);
  }
}

lemma computeGainRemoveLast(p: Problem, solution: Solution, i: int)
  requires isValidProblem(p)
  requires hasAllowedValues(solution)
  requires 0 <= i < |solution| <= |p.gains|
  requires i <= |solution[..|solution| - 1]| - 1

  ensures computeGain(p, solution, i) == computeGain(p, solution[..|solution| - 1], i)
{ 
  assert solution == solution[..|solution| - 1] + [solution[|solution| - 1]];
}

lemma gainAdd1(p: Problem, solution: Solution)
  requires isValidProblem(p)
  requires hasAllowedValues(solution)
  requires 0 < |solution| <= p.n
  requires solution[|solution| - 1] == 1

  ensures gain(p, solution) == gain(p, solution[..|solution| - 1]) + p.gains[|solution| - 1]
{ 
   if |solution| == 1 {

  } else {
    computeGainRemoveLast(p, solution, |solution[..|solution| - 1]| - 1);
    assert computeGain(p, solution, |solution[..|solution| - 1]| - 1) == 
           computeGain(p, solution[..|solution| - 1], |solution[..|solution| - 1]| - 1);
  }
}

lemma computeWeightRemoveLast(p: Problem, solution: Solution, i: int)
  requires isValidProblem(p)
  requires hasAllowedValues(solution)
  requires 0 <= i < |solution| <= |p.gains|
  requires solution == solution[..|solution| - 1] + [solution[|solution| - 1]] 
  requires i <= |solution[..|solution| - 1]| - 1

  ensures computeWeight(p, solution, i) == computeWeight(p, solution[..|solution| - 1], i)
{ }

lemma weightAdd1(p: Problem, solution: Solution)
  requires isValidProblem(p)
  requires hasAllowedValues(solution)
  requires 0 < |solution| <= p.n
  requires solution[|solution| - 1] == 1

  ensures weight(p, solution) == weight(p, solution[..|solution| - 1]) + p.weights[|solution| - 1]
{ 
  if |solution| == 1 {

  } else {
    computeWeightRemoveLast(p, solution, |solution[..|solution| - 1]| - 1);
    assert computeWeight(p, solution, |solution[..|solution| - 1]| - 1) == 
           computeWeight(p, solution[..|solution| - 1], |solution[..|solution| - 1]| - 1);
  }
}

lemma emptySolOptimal(p: Problem, solution: Solution, i: int, j: int)
 requires isValidProblem(p)
 requires 0 <= j <= p.c
 requires |solution| == i == 0
 requires isPartialSolution(p, solution, i, j)

 ensures isOptimalPartialSolution(p, solution, i, j)
{
  forall s: Solution  | isPartialSolution(p, s, i, j) && |solution| == |s|
  ensures gain(p, solution) >= gain(p, s) 
  { } 
  assert forall s: Solution :: ((isPartialSolution(p, s, i, j) && |s| == |solution|
     ==> gain(p, solution) >= gain(p, s)));
}

lemma computeWeightAllZeros(p: Problem, solution: Solution, i: int)
  requires isValidProblem(p)
  requires 0 <= i < |solution|
  requires 0 <= |solution| <= p.n 
  requires forall k :: 0 <= k < |solution| ==> solution[k] == 0
  
  ensures computeWeight(p, solution, i) == 0
{
  if i == 0 {
    assert  computeWeight(p, solution, i) == 0;
  } else {
    computeWeightAllZeros(p, solution, i - 1);
    assert computeWeight(p, solution, i - 1) == 0;
    assert computeWeight(p, solution, i) == 0;
  }
}

lemma computeGainAllZeros(p: Problem, solution: Solution, i: int)
  requires isValidProblem(p)
  requires 0 <= i < |solution|
  requires 0 <= |solution| <= p.n 
  requires forall k :: 0 <= k < |solution| ==> solution[k] == 0
  
  ensures computeGain(p, solution, i) == 0
{
  if i == 0 {
    assert  computeGain(p, solution, i) == 0;
  } else {
    computeGainAllZeros(p, solution, i - 1);
    assert computeGain(p, solution, i - 1) == 0;
    assert computeGain(p, solution, i) == 0;
  }
}

// lemma which proves that if a partial solution has weight 0, then any subsolution will have weight 0 as well
lemma {:induction false} computeWeightCapacity0(p: Problem, solution: Solution, i: int, idx: int, x: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires 0 <= |solution| <= p.n
 requires isPartialSolution(p, solution, i, 0)
 requires 0 <= x <= |solution| - 1
 requires computeWeight(p, solution, x) == 0
 requires 0 <= idx <= x
 
 ensures computeWeight(p, solution, idx) == 0
{
  if idx == x {
    assert computeWeight(p, solution, idx) == 0;
  } else {
    assert computeWeight(p, solution, x - 1) == 0 by 
    {
      assert 0 <= idx < x;
      assert computeWeight(p, solution, x) == 0;
      assert p.weights[x] > 0;
      assert 0 <= solution[x] <= 1;
      assert solution[x] * p.weights[x] >= 0;
      assert computeWeight(p, solution, x) == solution[x] * p.weights[x] + computeWeight(p, solution, x - 1);
    }
    computeWeightCapacity0(p, solution, i, idx, x - 1);
    assert computeWeight(p, solution, idx) == 0;
  }
}

// lemma which proves that if a partial solution for capacity 0 with only zeros will have a gain of 0
lemma gainCapacity0(p: Problem, solution: Solution, i: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires |solution| == i
 requires isPartialSolution(p, solution, i, 0)
 
 ensures gain(p, solution) == 0
{
  var idx: int := 0;
  while idx < |solution|
    invariant 0 <= idx <= |solution|
    invariant forall k :: 0 <= k < idx ==> solution[k] == 0
    invariant idx > 0 ==> computeWeight(p, solution, idx - 1) == 0
  {
    assert p.weights[idx] > 0;
    computeWeightCapacity0(p, solution, i, idx, |solution| - 1);
    assert p.weights[idx] > 0 && computeWeight(p, solution, idx) == 0 ==> solution[idx] == 0;
    idx := idx + 1;
  }
  assert forall k :: 0 <= k < |solution| ==> solution[k] == 0;
  computeGainAllZeros(p, solution, |solution| - 1);
  assert gain(p, solution) == 0;
}

// lemma which proves that for allowed capacity j = 0, a solution with gain 0 is optimal
lemma optimalSolCapacity0(p: Problem, solution: Solution, i: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires isPartialSolution(p, solution, i, 0)
 requires forall k :: 0 <= k < |solution| ==> solution[k] == 0
 requires weight(p, solution) == 0

 ensures isOptimalPartialSolution(p, solution, i, 0)
{
  assert isPartialSolution(p, solution, i, 0);
  forall s: Solution | isPartialSolution(p, s, i, 0) && |solution| == |s|
  ensures gain(p, solution) >= gain(p, s)
  {
    assert weight(p, solution) == 0;
    assert forall k :: 0 <= k < |solution| ==> solution[k] == 0;
    computeGainAllZeros(p, solution, |solution| - 1);
    gainCapacity0(p, s, i);
    assert gain(p, solution) == 0;
    assert gain(p, s) == 0;
  }
  assert forall s: Solution :: (isPartialSolution(p, s, i, 0) && |s| == |solution| ==> gain(p, solution) >= gain(p, s));
  assert isOptimalPartialSolution(p, solution, i, 0);
}

// this lemma is a helper for optimalSolAdd0, x is an assumed better solution than solution2 + [0], solution2 is the optimal solution when
// considering the first i - 1 objects; adding a zero to solution2 will obtain a profit as good as x
lemma gainAdd0Optimal(p: Problem, profit1: int, profit2: int, solution1: Solution, solution2: Solution, x: Solution, i: int, j: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires 0 <= j <= p.c
 requires p.weights[i - 1] <= j
 requires isOptimalPartialSolution(p, solution1, i - 1, j - p.weights[i - 1])
 requires isOptimalPartialSolution(p, solution2, i - 1, j)
 requires computeWeight(p, solution2 + [0], |solution2 + [0]| - 1) <= j
 requires profit1 == gain(p, solution1)
 requires profit2 == gain(p, solution2)
 requires p.gains[i - 1] + profit1 <= profit2
 requires isOptimalPartialSolution(p, x, i, j)
 requires x[i - 1] == 0

 ensures gain(p, x) == gain(p, solution2 + [0])
{
  var x' := x[..i - 1];
  assert x' == x[..|x| - 1];
  gainAdd0(p, x);
  assert gain(p, x) == gain(p, x[..i - 1]) == gain(p, x');

  optimalSolRemove0(p, x, i, j);
  assert isOptimalPartialSolution(p, x', i - 1, j);

  assert gain(p, x') == gain(p, solution2);
  
  gainAdd0(p, solution2 + [0]);
  assert gain(p, solution2) == gain(p, solution2 + [0]);

  gainAdd0(p, x);
  assert x == x' + [0];
  assert gain(p, x' + [0]) == gain(p, x) == gain(p, solution2 + [0]);
}

lemma optimalSolAdd0(p: Problem, profit1: int, profit2: int, solution1: Solution, solution2: Solution, i: int, j: int)
                                    // profit1 = profits[i - 1][j - p.weights[i - 1]] 
                                    // profit2 = profits[i - 1][j] 
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires 0 <= j <= p.c
 requires p.weights[i - 1] <= j
 requires isOptimalPartialSolution(p, solution1, i - 1, j - p.weights[i - 1])
 requires isOptimalPartialSolution(p, solution2, i - 1, j)
 requires computeWeight(p, solution2 + [0], |solution2 + [0]| - 1) <= j
 requires profit1 == gain(p, solution1)
 requires profit2 == gain(p, solution2)
 requires p.gains[i - 1] + profit1 <= profit2

 ensures isOptimalPartialSolution(p, solution2 + [0], i, j)
{
  if !isOptimalPartialSolution(p, solution2 + [0], i, j) {
    existsOptimalPartialSol(p, i, j);
    var x : Solution :| isOptimalPartialSolution(p, x, i, j);

    if x[i - 1] == 1 {
      var x' := x[..i - 1];
      assert gain(p, x') == profit1 by {
        optimalSolRemove1(p, x, i, j);
        assert x' == x[..|x| - 1];
        assert isOptimalPartialSolution(p, x', i - 1, j - p.weights[i - 1]);
      }
      gainAdd1(p, x);
      gainAdd0(p, solution2 + [0]);
      assert gain(p, x) == gain(p, x') + p.gains[i - 1] <= gain(p, solution2 + [0]);
      assert false;
    }
    assert x[i - 1] == 0;
    gainAdd0Optimal(p, profit1, profit2, solution1, solution2, x, i, j);
    assert gain(p, x) == gain(p, solution2 + [0]);
  }
}

// if the last element's weight is bigger than allowed capacity j then it means the last element must be 0
lemma gainAddTooBig(p: Problem, solution: Solution, i: int, j: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires 1 <= j <= p.c
 requires isPartialSolution(p, solution, i, j)
 requires |solution| >= 2
 requires p.weights[i - 1] > j

 ensures solution[i - 1] == 0
 ensures gain(p, solution[..i - 1]) == gain(p, solution)
 {
    if solution[i - 1] == 1 {
      assert computeWeight(p, solution, |solution| - 1) == 
        computeWeight(p, solution, |solution[..i]| - 1) + p.weights[i - 1];
      assert weight(p, solution) >= p.weights[i - 1] > j;
      assert !isPartialSolution(p, solution, i, j);
      assert false;
    }

    assert solution[i - 1] == 0;
    computeGainAdd0(p, solution, |solution| - 2);
    assert gain(p, solution[..i - 1]) == gain(p, solution);
}

lemma gainUpperBound(p: Problem, solution: Solution, i: int) 
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires 0 <= |solution| <= |p.gains|
 requires isValidPartialSolution(p, solution) && |solution| >= i 

 ensures computeGain(p, solution, i - 1) <= sumAllGains(p, i)
{
  var completeSol := seq(i, y => 1);
  assert forall q :: 0 <= q < i ==> completeSol[q] == 1;
  
  if i > 1 { 
    gainUpperBound(p, solution, i - 1);
    assert computeGain(p, solution, i - 2) <= sumAllGains(p, i - 1);
  } else {
  }
}

lemma existsOptimalPartialSol(p: Problem, i: int, j: int) 
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires 0 <= j <= p.c

 ensures exists s :: isOptimalPartialSolution(p, s, i, j)
{
  var k : int := 0;
  var completeSol := seq(i, y => 1);
  assert forall q :: 0 <= q < i ==> completeSol[q] == 1;
  var sum := sumAllGains(p, i);
  assert forall k :: 0 <= k < i ==> p.gains[k] > 0;

  if !exists s :: isOptimalPartialSolution(p, s, i, j) {
    var q := 0; 
    var currentSol := seq(i, y => 0);
    computeWeightAllZeros(p, currentSol, |currentSol| - 1);
    computeGainAllZeros(p, currentSol, |currentSol| - 1);
    assert computeGain(p, currentSol, |currentSol| - 1) == 0 >= q;
    assert sum == sumAllGains(p, i);

    while q < sum + 1
      invariant 0 <= q <= sum + 1
      invariant !exists s :: isOptimalPartialSolution(p, s, i, j)
      invariant !isOptimalPartialSolution(p, currentSol, i, j)
      invariant isPartialSolution(p, currentSol, i, j)
      invariant computeGain(p, currentSol, |currentSol| - 1) >= q
    {
      assert exists s_i :: isPartialSolution(p, s_i, i, j) && gain(p, s_i) > gain(p, currentSol);
      var s_i :| isPartialSolution(p, s_i, i, j) && gain(p, s_i) > gain(p, currentSol);
      
      currentSol := s_i;
      q := computeGain(p, s_i, |s_i| - 1);
      gainUpperBound(p, s_i, i);

    }
    
    assert computeGain(p, currentSol, |currentSol| - 1) >= sum + 1;
    gainUpperBound(p, currentSol, i);
    assert false;
  }
}

lemma optimalSolAdd0TooBig(p: Problem, solution: Solution, i: int, j: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires 1 <= j <= p.c
 requires isOptimalPartialSolution(p, solution, i - 1, j)
 requires computeWeight(p, solution + [0], |solution + [0]| - 1) <= j 
 requires p.weights[i - 1] > j

 ensures isOptimalPartialSolution(p, solution + [0], i, j)
{
  var s := solution + [0];
  weightAdd0(p, s);

  if !isOptimalPartialSolution(p, s, i, j) {
    existsOptimalPartialSol(p, i, j);
    var x : Solution :| isOptimalPartialSolution(p, x, i, j);

    gainAddTooBig(p, s, i, j);
    gainAddTooBig(p, x, i, j);
    var x1 := x[..i - 1];

    assert gain(p, x1) == gain(p, x) > gain(p, s);  
    assert gain(p, s) == gain(p, solution) < gain(p, x);
    assert gain(p, x1) > gain(p, solution);
    assert isPartialSolution(p, x, i, j);

    assert x[i - 1] == 0;
    computeWeightAdd0(p, x, |x| - 2);
    assert weight(p, x) == weight(p, x1);
    assert isPartialSolution(p, x1, i - 1, j);
    assert !isOptimalPartialSolution(p, solution, i - 1, j);
    assert false;
  }
}

// if solution is optimal for i objects and capacity j, if the last element which is 1 will be removed, 
// then solution remains optimal for i - 1 objects and capacity j - p.weights[i - 1]
lemma optimalSolRemove1(p: Problem, solution: Solution, i: int, j: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires 0 <= j <= p.c
 requires isOptimalPartialSolution(p, solution, i, j)
 requires solution[i - 1] == 1

 ensures isOptimalPartialSolution(p, solution[..i - 1], i - 1, j - p.weights[i - 1])
{
  var s' := solution[..i - 1];
  weightAdd1(p, solution);
  assert isPartialSolution(p, solution[..i - 1], i - 1, j - p.weights[i - 1]);

  if !isOptimalPartialSolution(p, solution[..i - 1], i - 1, j - p.weights[i - 1]) {
    gainAdd1(p, solution);
    existsOptimalPartialSol(p, i - 1, j - p.weights[i - 1]);
    var x : Solution :| isOptimalPartialSolution(p, x, i - 1, j - p.weights[i - 1]);
    assert |x| == |solution[..i - 1]|;
    assert gain(p, x) > gain(p, solution[..i - 1]);

    var x1 := x + [1];
    gainAdd1(p, x1);
    weightAdd1(p, x1);
    assert isOptimalPartialSolution(p, x1, i, j);
    assert s' == solution[..|solution| - 1];
    assert x == x1[..|x1| - 1];
    assert gain(p, x1) == gain(p, x) + p.gains[i - 1] > gain(p, s') + p.gains[i- 1] == gain(p, solution);
    assert gain(p, x1) > gain(p, solution);
    assert false;
  }
}

// if solution is optimal for i objects and capacity j, if the last element which is 0 will be removed, 
// then solution remains optimal for i - 1 objects and capacity j - p.weights[i - 1]
lemma optimalSolRemove0(p: Problem, solution: Solution, i: int, j: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires 0 <= j <= p.c
 requires isOptimalPartialSolution(p, solution, i, j)
 requires solution[i - 1] == 0

 ensures isOptimalPartialSolution(p, solution[..i - 1], i - 1, j)
{
  var s' := solution[..i - 1];
  weightAdd0(p, solution);
  assert isPartialSolution(p, solution[..i - 1], i - 1, j);

  if !isOptimalPartialSolution(p, solution[..i - 1], i - 1, j) {
    gainAdd0(p, solution);
    existsOptimalPartialSol(p, i - 1, j);
    var x : Solution :| isOptimalPartialSolution(p, x, i - 1, j);
    assert |x| == |solution[..i - 1]|;

    var x1 := x + [0];
    gainAdd0(p, x1);
    weightAdd0(p, x1);
    assert isOptimalPartialSolution(p, x1, i, j);
    assert s' == solution[..|solution| - 1];
    assert x == x1[..|x1| - 1];
    assert gain(p, x1) == gain(p, x) >= gain(p, s') == gain(p, solution);
    assert gain(p, x1) == gain(p, solution);
    assert false;
  }
}

// this lemma is a helper for optimalSolAdd1, x is an assumed better solution than solution1 + [1], solution1 is the optimal solution if
// the first i - 1 objects are taken; adding a one to solution1 will obtain a profit as good as x
lemma gainAdd1Optimal(p: Problem, profit1: int, profit2: int, solution1: Solution, solution2: Solution, x: Solution, i: int, j: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires 0 <= j <= p.c
 requires p.weights[i - 1] <= j
 requires isOptimalPartialSolution(p, solution1, i - 1, j - p.weights[i - 1])
 requires isOptimalPartialSolution(p, solution2, i - 1, j)
 requires computeWeight(p, solution1 + [1], |solution1 + [1]| - 1) <= j
 requires p.gains[i - 1] + profit1 > profit2
 requires isOptimalPartialSolution(p, x, i, j)
 requires x[i - 1] == 1

 ensures gain(p, x) == gain(p, solution1 + [1])
{
   assert gain(p, x) == gain(p, solution1 + [1]) by { 
      gainAdd1(p, solution1 + [1]);
      gainAdd1(p, x);
      assert x == x[..i - 1] + [1];
      assert gain(p, x[..i - 1]) == gain(p, solution1) by
      {
        optimalSolRemove1(p, x, i, j);
        assert isOptimalPartialSolution(p, x[..i - 1], i - 1, j - p.weights[i - 1]);
      } 
  }
}

lemma optimalSolAdd1(p: Problem, profit1: int, profit2: int, solution1: Solution, solution2: Solution, i: int, j: int)
                                    // profit1 = profits[i - 1][j - p.weights[i - 1]] 
                                    // profit2 = profits[i - 1][j] 
 requires isValidProblem(p)
 requires 1 <= i <= p.n
 requires 0 <= j <= p.c
 requires p.weights[i - 1] <= j
 requires isOptimalPartialSolution(p, solution1, i - 1, j - p.weights[i - 1])
 requires isOptimalPartialSolution(p, solution2, i - 1, j)
 requires computeWeight(p, solution1 + [1], |solution1 + [1]| - 1) <= j
 requires profit1 == gain(p, solution1)
 requires profit2 == gain(p, solution2)
 requires p.gains[i - 1] + profit1 > profit2

 ensures isOptimalPartialSolution(p, solution1 + [1], i, j)
{
  var s := solution1 + [1];

  if !isOptimalPartialSolution(p, s, i, j){
    existsOptimalPartialSol(p, i, j);
    var x : seq<int> :| isOptimalPartialSolution(p, x, i, j);

    assert gain(p, x) > gain(p, solution1 + [1]);
    if x[i - 1] == 0 {
      assert gain(p, x) <= profit2 by 
      {
        gainAdd0(p, x);
        assert gain(p, x[..i - 1]) == gain(p, x);
        weightAdd0(p, x);
        assert weight(p, x[..i - 1]) <= j;
      }
      assert gain(p, solution1 + [1]) > profit2 by 
      {
        gainAdd1(p, solution1 + [1]);
        assert gain(p, solution1 + [1]) == gain(p, solution1) + p.gains[i - 1];
      }
      assert false; 
    } else {
      gainAdd1Optimal(p, profit1, profit2, solution1, solution2, x, i, j);
      assert gain(p, x) == gain(p, solution1 + [1]);
    }
  }
}

// the optimal solution/obtained profit for the n objects and capacity c will be the last element from solutions/profits
method solve(p: Problem) returns (profit: int, solution: Solution)
  requires isValidProblem(p)
  
  ensures isSolution(p, solution)
  ensures isOptimalSolution(p, solution)
{
    var profits := []; 
    var solutions := [];
    var i := 0;

    var partialProfits, partialSolutions := solves0Objects(p, profits, solutions, i);
    profits := profits + [partialProfits];
    solutions := solutions + [partialSolutions];
    
    assert forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolution(p, partialSolutions[k], i, k);
    assert forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> gain(p, solutions[k][q]) == profits[k][q];

    i := i + 1;

    while i <= p.n 
      invariant 0 <= i <= p.n + 1
      invariant |profits| == |solutions| == i
      invariant forall k :: 0 <= k < i ==> |profits[k]| == p.c + 1

      invariant forall k :: 0 <= k < |solutions| ==> |solutions[k]| == p.c + 1
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> isOptimalPartialSolution(p, solutions[k][q], k, q)
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> gain(p, solutions[k][q]) == profits[k][q]
    {
        partialProfits, partialSolutions := getPartialProfits(p, profits, solutions, i);
        profits := profits + [partialProfits];
        solutions := solutions + [partialSolutions];
        i := i + 1; 
    }

    for i: int := 0 to |solutions|
    { 
      print solutions[i];
      print "\n";
    }
    
    solution := solutions[p.n][p.c];
    assert isOptimalSolution(p, solution);

    profit := profits[p.n][p.c];
}

// the case when no object is considered, optimal will be empty solutions with gain 0
method solves0Objects(p: Problem, profits: seq<seq<int>>, solutions : seq<seq<seq<int>>>, i: int) 
                  returns (partialProfits: seq<int>, partialSolutions: seq<seq<int>>)

  requires isValidProblem(p)
  requires |profits| == |solutions| == i == 0

  ensures |partialProfits| == p.c + 1
  ensures |partialSolutions| == p.c + 1
  ensures forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolution(p, partialSolutions[k], i, k)
  ensures forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]
{
        partialProfits := [];
        var j := 0;
        var currentSolution := [];
        partialSolutions := [];

         while j <= p.c
          invariant 0 <= j <= p.c + 1
          invariant |partialProfits| == j
          invariant |partialSolutions| == j

          invariant forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolution(p, partialSolutions[k], i, k)
          invariant forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]
        {
          partialProfits := partialProfits + [0];
          currentSolution := [];
          emptySolOptimal(p, currentSolution, i, j);
          assert isOptimalPartialSolution(p, currentSolution, i, j);
          partialSolutions := partialSolutions + [currentSolution];

          j := j + 1;
        }
}

method getPartialProfits(p: Problem, profits: seq<seq<int>>, solutions : seq<seq<seq<int>>>, i: int) 
                            returns (partialProfits: seq<int>, partialSolutions: seq<seq<int>>)
  requires isValidProblem(p)
  requires 0 < i < p.n + 1
  requires i == |profits| == |solutions|

  requires forall k :: 0 <= k < i ==> |profits[k]| == p.c + 1
  requires forall k :: 0 <= k < i ==> |solutions[k]| == p.c + 1
  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> isOptimalPartialSolution(p, solutions[k][q], k, q) 
  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> gain(p, solutions[k][q]) == profits[k][q]

  ensures p.c + 1 == |partialSolutions| == |partialProfits|
  ensures 0 <= |profits| <= p.n + 1 

  ensures forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolution(p, partialSolutions[k], i, k)
  ensures forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]
{
        var j := 0;
        partialProfits := [];
        partialSolutions := [];

        while j <= p.c
          invariant 0 <= j <= p.c + 1
          invariant 0 <= |profits| <= p.n + 1
          invariant j == |partialProfits| == |partialSolutions|

          invariant forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolution(p, partialSolutions[k], i, k)
          invariant forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]
        {
          if j == 0 {

              var currentProfit, currentSolution := solvesCapacity0(p, i, j);
              partialProfits := partialProfits + [currentProfit];
              partialSolutions := partialSolutions + [currentSolution];

              assert isOptimalPartialSolution(p, currentSolution, i, j);

          } else {
            if p.weights[i - 1] <= j {
              if p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]] > profits[i - 1][j] {

                  var currentProfit, currentSolution := solvesAdd1BetterProfit(p, profits, solutions, partialProfits, partialSolutions, i, j);
                  partialProfits := partialProfits + [currentProfit];
                  partialSolutions := partialSolutions + [currentSolution];

                  assert isOptimalPartialSolution(p, currentSolution, i, j);

              } else {

                  var currentProfit, currentSolution := solvesAdd0BetterProfit(p, profits, solutions, partialProfits, partialSolutions, i, j);
                  partialProfits := partialProfits + [currentProfit];
                  partialSolutions := partialSolutions + [currentSolution];

                  assert isOptimalPartialSolution(p, currentSolution, i, j);

              }
            } else {

                var currentProfit, currentSolution := solvesAdd0TooBig(p, profits, solutions, partialProfits, partialSolutions, i, j);
                partialProfits := partialProfits + [currentProfit];
                partialSolutions := partialSolutions + [currentSolution];

                assert isOptimalPartialSolution(p, currentSolution, i, j);

            }
          }
          j := j + 1;
          
        }
}

// the case when allowed capacity is 0, so no object can be taken since every object's weight is bigger than 0
method solvesCapacity0(p: Problem, i: int, j: int) returns (currentProfit: int, currentSolution: Solution)
  requires isValidProblem(p)
  requires 1 <= i <= p.n
  requires j == 0

  ensures isOptimalPartialSolution(p, currentSolution, i, j)
  ensures currentProfit == gain(p, currentSolution)               
{
    currentProfit := 0;
    currentSolution := seq(i, y => 0);

    computeWeightAllZeros(p, currentSolution, |currentSolution| - 1);

    optimalSolCapacity0(p, currentSolution, i);
    gainCapacity0(p, currentSolution, i);
    
    assert isOptimalPartialSolution(p, currentSolution, i, j);
}

// the case when a better profit is obtained if the object is taken into the knapsack
method solvesAdd1BetterProfit(p: Problem, profits: seq<seq<int>>, solutions: seq<seq<seq<int>>>, partialProfits: seq<int>, partialSolutions: seq<seq<int>>, 
                             i: int, j: int) returns (currentProfit: int, currentSolution: seq<int>)

  requires isValidSubproblem(p, i, j)
  requires areValidSolutions(p, profits, solutions, i)
  requires areValidPartialSolutions(p, profits, solutions, partialProfits, partialSolutions, i, j)
  
  requires p.weights[i - 1] <= j
  requires p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]] > profits[i - 1][j]

  ensures isOptimalPartialSolution(p, currentSolution, i, j)
  ensures currentProfit == gain(p, currentSolution)       
{
    currentProfit := p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]];
    currentSolution := solutions[i - 1][j - p.weights[i - 1]];
    
    computeWeightFits1(p, currentSolution, i - 1, j);

    optimalSolAdd1(p, profits[i - 1][j - p.weights[i - 1]], profits[i - 1][j], 
      currentSolution, solutions[i - 1][j], i, j);

    currentSolution := currentSolution + [1];

    gainAdd1(p, currentSolution);

    assert isOptimalPartialSolution(p, currentSolution, i, j);        
}

// the case when a better profit is not obtained if the object is taken into the knapsack
method solvesAdd0BetterProfit(p: Problem, profits: seq<seq<int>>, solutions: seq<seq<seq<int>>>, partialProfits: seq<int>, partialSolutions: seq<seq<int>>, 
                             i: int, j: int) returns (currentProfit: int, currentSolution: seq<int>)

  requires isValidSubproblem(p, i, j)
  requires areValidSolutions(p, profits, solutions, i)
  requires areValidPartialSolutions(p, profits, solutions, partialProfits, partialSolutions, i, j)
  
  requires p.weights[i - 1] <= j
  requires p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]] <= profits[i - 1][j]

  ensures isOptimalPartialSolution(p, currentSolution, i, j)
  ensures currentProfit == gain(p, currentSolution)          
{
    currentProfit := profits[i - 1][j];
    currentSolution := solutions[i - 1][j];

    computeWeightFits0(p, currentSolution, j);

    optimalSolAdd0(p, profits[i - 1][j - p.weights[i - 1]], profits[i - 1][j], 
      solutions[i - 1][j - p.weights[i - 1]], currentSolution, i, j);

    currentSolution := currentSolution + [0];
    
    gainAdd0(p, currentSolution);

    assert isOptimalPartialSolution(p, currentSolution, i, j);   
}

// the case when the weight of the object will exceed the knapsack capacity j
method solvesAdd0TooBig(p: Problem, profits: seq<seq<int>>, solutions: seq<seq<seq<int>>>, partialProfits: seq<int>, partialSolutions: seq<seq<int>>, 
                       i: int, j: int) returns (currentProfit: int, currentSolution: seq<int>)

  requires isValidSubproblem(p, i, j)
  requires areValidSolutions(p, profits, solutions, i)
  requires areValidPartialSolutions(p, profits, solutions, partialProfits, partialSolutions, i, j)

  requires p.weights[i - 1] > j

  ensures isOptimalPartialSolution(p, currentSolution, i, j)
  ensures currentProfit == gain(p, currentSolution)     
{
    currentProfit := profits[i - 1][j];
    currentSolution := solutions[i - 1][j];

    computeWeightFits0(p, currentSolution, j);

    optimalSolAdd0TooBig(p, currentSolution, i, j);

    currentSolution := currentSolution + [0];
    
    gainAdd0(p, currentSolution);

    assert isOptimalPartialSolution(p, currentSolution, i, j);        
}

method main()
{
    var p: Problem := Problem(n := 4, c := 8, 
                                    gains := [1, 2, 5, 6], weights := [2, 3, 4, 5]);
    var maximProfit, finalSolution := solve(p);

    print "\n Maxim profit is: ";
    print maximProfit;

    print "\n Optimal solution is: ";
    print finalSolution;
}