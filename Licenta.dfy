datatype Problem = Problem(numberOfObjects: int, knapsackCapacity: int, gains: seq<int>, weights: seq<int>)

predicate hasPositiveValues(input: seq<int>)
{
    forall i :: 0 <= i < |input| ==> input[i] > 0
}

predicate hasOnlyPermittedValues(solution: seq<int>)
{
  forall k :: 0 <= k < |solution| ==> solution[k] == 0 || solution[k] == 1
}

predicate isValidProblem(p: Problem)
{
    |p.gains| == |p.weights| == p.numberOfObjects && 
    p.numberOfObjects > 0 && p.knapsackCapacity >= 0 && 
    hasPositiveValues(p.gains) && hasPositiveValues(p.weights) 
}

function gain(p: Problem, solution: seq<int>): int
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(solution)
  requires 0 <= |solution| <= p.numberOfObjects

  ensures gain(p, solution) == if |solution| == 0 then 0 else computeGain(p.gains, solution, |solution| - 1)
{
  if |solution| == 0 then 0 else computeGain(p.gains, solution, |solution| - 1)
}

function computeGain(gains: seq<int>, solution: seq<int>, i: int) : int
  requires 0 <= i < |solution|
  requires 0 <= i < |gains|
  requires hasOnlyPermittedValues(solution)
  requires 0 <= |solution| <= |gains|

  ensures computeGain(gains, solution, i) == if i == 0 then solution[0] * gains[0] else solution[i] * gains[i] + computeGain(gains, solution, i - 1)
{
  if i == 0 then solution[0] * gains[0] else solution[i] * gains[i] + computeGain(gains, solution, i - 1)
}

function computeGainNew(p: Problem , solution: seq<int>, i: int) : int
  requires isValidProblem(p)
  requires 0 <= i < |solution|
  requires 0 <= i < |p.gains|
  requires hasOnlyPermittedValues(solution)
  requires 0 <= |solution| <= |p.gains|
  
  ensures computeGainNew(p, solution, i) == if i == 0 then solution[0] * p.gains[0] else solution[i] * p.gains[i] + computeGainNew(p, solution, i - 1)
  ensures computeGainNew(p, solution, i) == computeGain(p.gains, solution, i)
  ensures computeGainNew(p, solution, i) >= 0
{
   if i == 0 then solution[0] * p.gains[0] else solution[i] * p.gains[i] + computeGainNew(p, solution, i - 1)
}

function weight(p: Problem, solution: seq<int>): int
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(solution)
  requires 0 <= |solution| <= p.numberOfObjects
  
  ensures weight(p, solution) == if |solution| == 0 then 0 else computeWeight(p.weights, solution, |solution| - 1)
{
  if |solution| == 0 then 0 else computeWeight(p.weights, solution, |solution| - 1)
}

function computeWeight(weights: seq<int>, solution: seq<int>, i: int) : int
 requires forall i :: 0 <= i < |weights| ==> weights[i] > 0 
  requires 0 <= i < |solution|
  requires 0 <= i < |weights|
  requires hasOnlyPermittedValues(solution)
  requires 0 <= |solution| <= |weights|
  
  ensures computeWeight(weights, solution, i) == if i == 0 then solution[0] * weights[0] else solution[i] * weights[i] + computeWeight(weights, solution, i - 1)
  ensures computeWeight(weights, solution, i) >= 0
{
   if i == 0 then solution[0] * weights[0] else solution[i] * weights[i] + computeWeight(weights, solution, i - 1)
}

predicate isValidPartialSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
{
  hasOnlyPermittedValues(solution)
}

predicate isPartialSolutionOfFirstIObjectsAndWeightJ(p: Problem, solution: seq<int>, i: int, j: int)
  requires isValidProblem(p)
  requires 0 <= i <= p.numberOfObjects
  requires 0 <= j <= p.knapsackCapacity
{
  isValidPartialSolution(p, solution) && |solution| == i &&
  weight(p, solution) <= j
}

predicate isPartialSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
{ 
  isPartialSolutionOfFirstIObjectsAndWeightJ(p, solution, p.numberOfObjects, p.knapsackCapacity)
}

predicate isSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
{
  isValidPartialSolution(p, solution) && |solution| == p.numberOfObjects &&
  weight(p, solution) <= p.knapsackCapacity
}

ghost predicate isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p: Problem, solution: seq<int>, i: int, j: int)
  requires isValidProblem(p)
  requires 0 <= i <= p.numberOfObjects
  requires 0 <= j <= p.knapsackCapacity
{
  isPartialSolutionOfFirstIObjectsAndWeightJ(p, solution, i, j) &&
  forall s: seq<int> :: (isPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j) && |s| == |solution| ==> gain(p, solution) >= gain(p, s))
}

ghost predicate isOptimalPartialSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
{
    isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, solution, p.numberOfObjects, p.knapsackCapacity)
}

ghost predicate isOptimalSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
  requires isValidPartialSolution(p, solution)
{
    isOptimalPartialSolution(p, solution) &&
    forall s: seq<int> :: (((isOptimalPartialSolution(p, s)) ==> 
    gain(p, solution) >= gain(p, s)))
}

lemma AddingObjectDoesNotExceedsCapacity(p: Problem, i: int, j: int, sol: seq<int>)  
  requires isValidProblem(p)
  requires 0 <= |sol| < p.numberOfObjects
  requires 0 <= i < |p.weights|
  requires hasOnlyPermittedValues(sol)
  requires 0 <= j <= p.knapsackCapacity + 1
  requires weight(p, sol) <= j - p.weights[i]
  requires i == |sol|
  
  ensures computeWeight(p.weights, sol + [1], |sol + [1]| - 1) <= j
{
  var newSol := sol + [1];
  assert sol == newSol[..|newSol| - 1];

  for a := 0 to |newSol[..|newSol| - 1]|
    invariant 0 <= a <= |newSol[..|newSol| - 1]| + 1
    invariant forall k :: 0 <= k < a ==> computeWeight(p.weights, sol, k) == computeWeight(p.weights, newSol, k)
  {
    assert computeWeight(p.weights, sol, a) == computeWeight(p.weights, newSol, a);
  }
}

lemma NotAddingObjectDoesNotChangeSolWeight(p: Problem, j: int, sol: seq<int>)
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(sol)
  requires 0 <= |sol| < p.numberOfObjects
  requires weight(p, sol) <= j
  
  ensures computeWeight(p.weights, sol + [0], |sol + [0]| - 1) <= j 
{  
  if |sol| == 0 {
    assert weight(p, sol) <= j;
  } else {
    var newSol := sol + [0];
    assert newSol[..|newSol| - 1] == sol;
    LastElementIs0ForComputeWeightHelper(p, newSol, |newSol| - 2);
    assert computeWeight(p.weights, sol + [0], |sol + [0]| - 1) <= j;
  }
}

lemma LastElementIs0ForComputeWeightHelper(p: Problem, sol: seq<int>, i: int)
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(sol)
  requires 0 <= i < |sol| - 1
  requires 0 <= i < |p.weights|
  requires 0 <= |sol| <= |p.weights|
  requires sol[|sol| - 1] == 0
  
  ensures computeWeight(p.weights, sol, i) == computeWeight(p.weights, sol[..|sol| - 1], i)
{ }

lemma LastElementIs0ForWeightHelper(p: Problem, sol: seq<int>)
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(sol)
  requires 0 < |sol| <= p.numberOfObjects
  requires sol[|sol| - 1] == 0
  
  ensures weight(p, sol) == weight(p, sol[..|sol| - 1])
{
  if |sol| == 1 {

  } else {
    assert computeWeight(p.weights, sol, |sol| - 1) == computeWeight(p.weights, sol, |sol| - 2);
    LastElementIs0ForComputeWeightHelper(p, sol, |sol| - 2);
  }
 }

lemma LastElementIs0ForComputeGainHelper(p: Problem, sol: seq<int>, i: int)
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(sol)
  requires 0 <= i < |sol| - 1
  requires 0 <= i < |p.gains|
  requires 0 <= |sol| <= |p.gains|
  requires sol[|sol| - 1] == 0
  
  ensures computeGain(p.gains, sol, i) == computeGain(p.gains, sol[..|sol| - 1], i)
{ }

lemma LastElementIs0ForGainHelper(p: Problem, sol: seq<int>)
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(sol)
  requires 0 < |sol| <= p.numberOfObjects
  requires sol[|sol| - 1] == 0
  
  ensures gain(p, sol) == gain(p, sol[..|sol| - 1])
{ 
  if |sol| == 1 {

  } else {
    assert computeGain(p.gains, sol, |sol| - 1) == computeGain(p.gains, sol, |sol| - 2);
    LastElementIs0ForComputeGainHelper(p, sol, |sol| - 2);
  }
}

lemma ComputeGainHelper(p: Problem, sol: seq<int>, i: int) 
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(sol)
  requires 0 <= i < |sol| <= |p.gains|
  requires sol == sol[..|sol| - 1] + [sol[|sol| - 1]] 
  requires i <= |sol[..|sol| - 1]| - 1

  ensures computeGain(p.gains, sol, i) == computeGain(p.gains, sol[..|sol| - 1], i)
{
  // for j := 0 to i 
  // invariant computeGain(p.gains, sol, j) == computeGain(p.gains, sol[..|sol| - 1], j)
  // { }
  // if (i == 0) {
  // } else {
  //   ComputeGainHelper(p, sol, i - 1);
  // }
}

lemma LastElementIs1ForGainHelper(p: Problem, sol: seq<int>)
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(sol)
  requires 0 < |sol| <= p.numberOfObjects
  requires sol[|sol| - 1] == 1

  ensures gain(p, sol) == gain(p, sol[..|sol| - 1]) + p.gains[|sol| - 1]
{ 
   if |sol| == 1 {

  } else {
    ComputeGainHelper(p, sol, |sol[..|sol| - 1]| - 1);
    assert computeGain(p.gains, sol, |sol[..|sol| - 1]| - 1) == computeGain(p.gains, sol[..|sol| - 1], |sol[..|sol| - 1]| - 1);
  }
}

lemma ComputeWeightHelper(p: Problem, sol: seq<int>, i: int) 
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(sol)
  requires 0 <= i < |sol| <= |p.gains|
  requires sol == sol[..|sol| - 1] + [sol[|sol| - 1]] 
  requires i <= |sol[..|sol| - 1]| - 1

  ensures computeWeight(p.weights, sol, i) == computeWeight(p.weights, sol[..|sol| - 1], i)
{ }

lemma LastElementIs1ForWeightHelper(p: Problem, sol: seq<int>)
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(sol)
  requires 0 < |sol| <= p.numberOfObjects
  requires sol[|sol| - 1] == 1

  ensures weight(p, sol) == weight(p, sol[..|sol| - 1]) + p.weights[|sol| - 1]
{ 
  if |sol| == 1 {

  } else {
    ComputeWeightHelper(p, sol, |sol[..|sol| - 1]| - 1);
    assert computeWeight(p.weights, sol, |sol[..|sol| - 1]| - 1) == computeWeight(p.weights, sol[..|sol| - 1], |sol[..|sol| - 1]| - 1);
  }
}

lemma emptySolutionIsOptimal(p: Problem, sol: seq<int>, i: int, j: int)
 requires isValidProblem(p)
 requires 0 <= j <= p.knapsackCapacity
 requires |sol| == i == 0
 requires isPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i, j)

 ensures isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i, j)
{
  forall s: seq<int>  | isPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j) && |sol| == |s|
  ensures gain(p, sol) >= gain(p, s) 
  { } 
  assert forall s: seq<int> :: ((isPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j) && |s| == |sol| ==> gain(p, sol) >= gain(p, s)));
}

lemma Weight0Lemma(p: Problem, sol: seq<int>, i: int)
  requires isValidProblem(p)
  requires 0 <= i < |sol|
  requires 0 <= i < |p.weights|
  requires 0 <= |sol| <= p.numberOfObjects 
  requires forall k :: 0 <= k < |sol| ==> sol[k] == 0
  
  ensures computeWeight(p.weights, sol, i) == 0
{
  if i == 0 {
    assert  computeWeight(p.weights, sol, i) == 0;
  } else {
    Weight0Lemma(p, sol, i - 1);
    assert computeWeight(p.weights, sol, i - 1) == 0;
    assert computeWeight(p.weights, sol, i) == 0;
  }
}

lemma Gain0Lemma(p: Problem, sol: seq<int>, i: int)
  requires isValidProblem(p)
  requires 0 <= i < |sol|
  requires 0 <= i < |p.gains|
  requires 0 <= |sol| <= p.numberOfObjects 
  requires forall k :: 0 <= k < |sol| ==> sol[k] == 0
  
  ensures computeGain(p.gains, sol, i) == 0
{
  if i == 0 {
    assert  computeGain(p.gains, sol, i) == 0;
  } else {
    Gain0Lemma(p, sol, i - 1);
    assert computeGain(p.gains, sol, i - 1) == 0;
    assert computeGain(p.gains, sol, i) == 0;
  }
}

lemma SubsolutionWeightIsZero(p: Problem, sol: seq<int>, i:int, j: int, idx: int, n : int)
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects
 requires 0 <= |sol| <= p.numberOfObjects
 requires j == 0
 requires isPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i, j)
 requires 0 <= n <= |sol| - 1
 requires computeWeight(p.weights, sol, n) == 0
 requires 0 <= idx <= n
 
 ensures computeWeight(p.weights, sol, idx) == 0
{
  assume false;
  assert computeWeight(p.weights, sol, n) == 0;

  if idx == n {
    // assert (computeWeight(p.weights, sol, |sol| - 1) == 0 && (forall k :: 0 <= k < |p.weights| ==> p.weights[k] > 0)) ==>
    //         sol[0] * p.weights[0] == 0;
    // assert computeWeight(p.weights, sol, idx) == 0;
  } else {
    assert n > 0;
    assert 0 <= idx < n;
    assert computeWeight(p.weights, sol, n) == 0;
    assert p.weights[n] > 0;
    assert 0 <= sol[n] <= 1;
    assert sol[n] * p.weights[n] >= 0;
    assert computeWeight(p.weights, sol, n) == sol[n] * p.weights[n] + computeWeight(p.weights, sol, n - 1);
    assert computeWeight(p.weights, sol, n - 1) == 0;
    SubsolutionWeightIsZero(p, sol, i, j, idx, n - 1);
    assert computeWeight(p.weights, sol, idx) == 0;
  }

  assert computeWeight(p.weights, sol, idx) == 0;
}

lemma Weight0ImpliesGain0(p: Problem, sol: seq<int>, i:int, j: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects
 requires |sol| == i
 requires j == 0
 requires isPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i, j)
 requires weight(p, sol) == 0
 
 ensures gain(p, sol) == 0
{
  var idx: int := 0;
  while idx < |sol|
    invariant 0 <= idx <= |sol|
    invariant forall k :: 0 <= k < idx ==> sol[k] == 0
    invariant idx > 0 ==> computeWeight(p.weights, sol, idx - 1) == 0
  {
    assert p.weights[idx] > 0;
    SubsolutionWeightIsZero(p, sol, i, j, idx, |sol| - 1);
    assert p.weights[idx] > 0 && computeWeight(p.weights, sol, idx) == 0 ==> sol[idx] == 0;
    idx := idx + 1;
  }
  assert forall k :: 0 <= k < |sol| ==> sol[k] == 0;
  Gain0Lemma(p, sol, |sol| - 1);
  assert gain(p, sol) == 0;
}

lemma MaximumWeightAllowedIs0(p: Problem, sol: seq<int>, i: int, j: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects
 requires 1 <= i <= |p.gains|
 requires j == 0
 requires isPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i, j)
 requires forall k :: 0 <= k < |sol| ==> sol[k] == 0
 requires weight(p, sol) == 0

 ensures isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i, j)
{
  assert isPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i, j);
  forall s: seq<int> | isPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j) && |sol| == |s|
  ensures gain(p, sol) >= gain(p, s)
  {
    assert weight(p, sol) == 0 <= j;
    assert forall k :: 0 <= k < |sol| ==> sol[k] == 0;
    Gain0Lemma(p, sol, |sol| - 1);
    Weight0ImpliesGain0(p, s, i, j);
    assert gain(p, sol) == 0;
    assert gain(p, s) == 0;
  }
  assert forall s: seq<int> :: (isPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j) && |s| == |sol| ==> gain(p, sol) >= gain(p, s));
  assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i, j);
}

method KnapsackProblem(p: Problem) returns (profit: int, solution: seq<int>)
  requires isValidProblem(p)
  
  ensures isSolution(p, solution)
  ensures isOptimalSolution(p, solution)
{
    var profits := []; 
    var solutions := [];
    var i := 0;

    var partialProfits, partialSolutions := FillMatrixForObject0(p, profits, solutions, i);
    profits := profits + [partialProfits];
    solutions := solutions + [partialSolutions];
    assert forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> weight(p, solutions[k][q]) <= q;
    assert forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == i;
    assert forall k :: 0 <= k < |partialSolutions| ==> isPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k);

    assert forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i ,k);
    assert forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> gain(p, solutions[k][q]) == profits[k][q];

    i := i + 1;

    while i <= p.numberOfObjects 
      invariant |profits| == |solutions| == i
      invariant 0 <= i <= p.numberOfObjects + 1
      invariant forall k :: 0 <= k < i ==> |profits[k]| == p.knapsackCapacity + 1
      invariant 0 <= |profits| <= p.numberOfObjects + 1

      invariant forall k :: 0 <= k < |solutions| ==> |solutions[k]| == p.knapsackCapacity + 1
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == k
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> hasOnlyPermittedValues(solutions[k][q])
      invariant forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> 0 <= |solutions[k][q]| <= p.numberOfObjects

      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                        isPartialSolutionOfFirstIObjectsAndWeightJ(p, solutions[k][q], k, q)

      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, solutions[k][q], k, q)
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                gain(p, solutions[k][q]) == profits[k][q]
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
    
    solution := solutions[p.numberOfObjects][p.knapsackCapacity];
    assert weight(p, solution) <= p.knapsackCapacity;
    assert isPartialSolution(p, solution);
    assert isSolution(p, solution);

    assert isOptimalPartialSolution(p, solution);
    assert isOptimalSolution(p, solution);

    profit := profits[p.numberOfObjects][p.knapsackCapacity];
}

method FillMatrixForObject0(p: Problem, profits: seq<seq<int>>, solutions : seq<seq<seq<int>>>, i: int) returns (partialProfits: seq<int>, partialSolutions: seq<seq<int>>)
  requires isValidProblem(p)
  requires |profits| == |solutions| == i == 0

  ensures |partialProfits| == p.knapsackCapacity + 1
  ensures |partialSolutions| == p.knapsackCapacity + 1
  ensures forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == i
  ensures forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
  ensures forall k :: 0 <= k < |partialSolutions| ==> weight(p, partialSolutions[k]) <= k
  ensures forall k :: 0 <= k < |partialSolutions| ==> forall q :: 0 <= q < |partialSolutions[k]| ==> partialSolutions[k][q] == 0
  ensures forall k :: 0 <= k < |partialSolutions| ==> isPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k)

  ensures forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k)
  ensures forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]
{
        partialProfits := [];
        var j := 0;
        var currentSolution := [];
        partialSolutions := [];

        assert weight(p, currentSolution) == 0;

         while j <= p.knapsackCapacity
          invariant 0 <= j <= p.knapsackCapacity + 1
          invariant |partialProfits| == j
          invariant |partialSolutions| == j

          invariant |partialSolutions| > 0 ==> forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == i 
          invariant forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
          invariant forall k :: 0 <= k < |partialSolutions| ==> weight(p, partialSolutions[k]) <= k
          invariant forall k :: 0 <= k < |partialSolutions| ==> forall q :: 0 <= q < |partialSolutions[k]| ==> partialSolutions[k][q] == 0
          invariant forall k :: 0 <= k < |partialSolutions| ==> isPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k)

          invariant forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k)
          invariant forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]
        {
              partialProfits := partialProfits + [0];
              currentSolution := [];
              emptySolutionIsOptimal(p, currentSolution, i, j);
              assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j);
              partialSolutions := partialSolutions + [currentSolution];

              assert |currentSolution| == i;
              assert weight(p, currentSolution) <= j;

              j := j + 1;
        }
}

lemma NotTakingObjectLeadsToOptimalCase1(p: Problem, profit1: int, profit2: int, sol1: seq<int>, sol2:seq<int>, i: int, j: int) 
                                    // profit1 = profits[i - 1][j - p.weights[i - 1]] 
                                    // profit2 = profits[i - 1][j] 
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects
 requires 0 <= j <= p.knapsackCapacity
 requires p.weights[i - 1] <= j
 requires isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol1, i - 1, j - p.weights[i - 1])
 requires isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol2, i - 1, j)
 requires computeWeight(p.weights, sol2 + [0], |sol2 + [0]| - 1) <= j
 requires profit1 == gain(p, sol1)
 requires profit2 == gain(p, sol2)
 requires p.gains[i - 1] + profit1 <= profit2

 ensures isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol2 + [0], i, j)
{
  if !isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol2 + [0], i, j){
    ExistsOptimalPartialSolution(p, i, j);
    //assert exists s :: isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j);
    var x : seq<int> :| isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, x, i, j);
    assume false;
  }
}

lemma LastElemIs0AndGainIsUnchanged(p: Problem, sol: seq<int>, i: int, j: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects
 requires 1 <= i <= |p.gains|
 requires 1 <= j <= p.knapsackCapacity
 requires isPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i, j)
 requires |sol| >= 2
 requires p.weights[i - 1] > j

 ensures sol[i - 1] == 0
 ensures gain(p, sol[..i - 1]) == gain(p, sol)
 {
    if sol[i - 1] == 1 {
      assert computeWeight(p.weights, sol, |sol| - 1) == computeWeight(p.weights, sol, |sol[..i]| - 1) + p.weights[i - 1];
      assert weight(p, sol) >= p.weights[i - 1] > j;
      assert !isPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i, j);
      assert false;
    }

    assert sol[i - 1] == 0;
    LastElementIs0ForComputeGainHelper(p, sol, |sol| - 2);
    assert gain(p, sol[..i - 1]) == gain(p, sol);
}

function MaximumGain(p: Problem, i: int) : int
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects

 ensures MaximumGain(p, i) >= 0
{
  if (i == 1) then p.gains[0] else p.gains[i - 1] + MaximumGain(p, i -1)
}

lemma GainUpperBound(p: Problem, i: int, s: seq<int>) 
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects
 requires 0 <= |s| <= |p.gains|
 requires isValidPartialSolution(p, s) && |s| >= i 

 ensures computeGainNew(p, s, i - 1) <= MaximumGain(p, i)
{
  var completeSol := seq(i, w => 1);
  assert forall q :: 0 <= q < i ==> completeSol[q] == 1;
  var sumAllGains := computeGainNew(p, completeSol, |completeSol| - 1);
  if i > 1 { 
    GainUpperBound(p, i - 1, s);
    assert computeGainNew(p, s, i - 2) <= MaximumGain(p, i - 1);
  } else {
  }
}

lemma ExistsOptimalPartialSolution(p: Problem, i: int, j: int) 
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects
 requires 0 <= j <= p.knapsackCapacity

 ensures exists s :: isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j)
{
  assume false;
  var k : int := 0;
  var completeSol := seq(i, w => 1);
  assert forall q :: 0 <= q < i ==> completeSol[q] == 1;
  var sumAllGains := MaximumGain(p, i);
  assert forall k :: 0 <= k < i ==> p.gains[k] > 0;

  if !exists s :: isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j) {
    var q := 0; 
    var currentSol := seq(i, w => 0);
    Weight0Lemma(p, currentSol, |currentSol| - 1);
    assert isPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSol, i, j);
    Gain0Lemma(p, currentSol, |currentSol| - 1);
    assert computeGain(p.gains, currentSol, |currentSol| - 1) == 0 >= q;
    assert sumAllGains == MaximumGain(p, i);

    while q < sumAllGains + 1
      invariant 0 <= q <= sumAllGains + 1
      invariant !exists s :: isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j)
      invariant !isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSol, i, j)
      invariant isPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSol, i, j)
      invariant computeGain(p.gains, currentSol, |currentSol| - 1) >= q
    {
      assert exists s_i :: isPartialSolutionOfFirstIObjectsAndWeightJ(p, s_i, i, j) && gain(p, s_i) > gain(p, currentSol);
      var s_i :| isPartialSolutionOfFirstIObjectsAndWeightJ(p, s_i, i, j) && gain(p, s_i) > gain(p, currentSol);
      
      currentSol := s_i;
      q := computeGain(p.gains, s_i, |s_i| - 1);
      GainUpperBound(p, i,  s_i);

    }
    
    assert computeGainNew(p, currentSol, |currentSol| - 1) >= sumAllGains + 1;
    GainUpperBound(p, i,  currentSol);
    assert false;
  }
}

lemma NotTakingObjectLeadsToOptimalCase2(p: Problem, sol: seq<int>, i: int, j: int) // sol is solutions[i - 1][j]
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects
 requires 1 <= j <= p.knapsackCapacity
 requires isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i - 1, j)
 requires computeWeight(p.weights, sol + [0], |sol + [0]| - 1) <= j 
 requires p.weights[i - 1] > j

 ensures isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol + [0], i, j)
{
  // assume false;
  var s := sol + [0];
  LastElementIs0ForWeightHelper(p, s);

  if !isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j) {
    assert isPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j);
    assert !isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j);
    
    // assume exists x :: isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, x, i, j);
    ExistsOptimalPartialSolution(p, i, j);
    assert isValidProblem(p);
    assert 1 <= i <= p.numberOfObjects;
    assert 0 <= j <= p.knapsackCapacity;
    assert exists s :: isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j);

    var x : seq<int> :| isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, x, i, j);

    LastElemIs0AndGainIsUnchanged(p, s, i, j);
    assert gain(p, s[..i - 1]) == gain(p, s); 

    LastElemIs0AndGainIsUnchanged(p, x, i, j);
    var x1 := x[..i - 1];

    assert gain(p, x1) == gain(p, x) > gain(p, s);  
    assert gain(p, s) == gain(p, sol) < gain(p, x);
    assert gain(p, x1) > gain(p, sol);
    
    assert isPartialSolutionOfFirstIObjectsAndWeightJ(p, x, i, j);
    assert x[i - 1] == 0;
    LastElementIs0ForComputeWeightHelper(p, x, |x| - 2);
    assert weight(p, x) == weight(p, x1);
    assert isPartialSolutionOfFirstIObjectsAndWeightJ(p, x1, i - 1, j);
    assert !isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol, i - 1, j);
    assert false;
  }
}

lemma OptimalSubsolution(p: Problem, s: seq<int>, i: int, j: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects
 requires 0 <= j <= p.knapsackCapacity
 requires isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j)
 requires s[i - 1] == 1

 ensures isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, s[..i - 1], i - 1, j - p.weights[i - 1])
{
  assume false;
   if s[i - 1] == 1 {
    // assume false;
  } else {
    assert s[i - 1] == 0;
    LastElementIs0ForWeightHelper(p, s);
    assert weight(p, s) == weight(p, s[..i - 1]) <= j;
    LastElementIs0ForGainHelper(p, s);
    assert gain(p, s) == gain(p, s[..i - 1]);
    // assume false;
    assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, s[..i - 1], i - 1, j);
  }
}

lemma AddingObjHasEqualGainAsOptimalSol(p: Problem, profit1: int, profit2: int, sol1: seq<int>, sol2:seq<int>, x: seq<int>, i: int, j: int)
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects
 requires 0 <= j <= p.knapsackCapacity
 requires p.weights[i - 1] <= j
 requires isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol1, i - 1, j - p.weights[i - 1])
 requires isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol2, i - 1, j)
 requires computeWeight(p.weights, sol1 + [1], |sol1 + [1]| - 1) <= j
 requires p.gains[i - 1] + profit1 > profit2
 requires isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, x, i, j)
 requires x[i - 1] == 1

 ensures gain(p, x) == gain(p, sol1 + [1])
{
  //  assume false;
   assert gain(p, x) == gain(p, sol1 + [1]) by { 
      LastElementIs1ForGainHelper(p, sol1 + [1]);
      LastElementIs1ForGainHelper(p, x);
      assert x == x[..i - 1] + [1];
      assert gain(p, x[..i - 1]) == gain(p, sol1) by
      {
        OptimalSubsolution(p, x, i, j);
        assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, x[..i - 1], i - 1, j - p.weights[i - 1]);
      } 
  }
}

lemma CaseTakingObjectLeadsToOptimal(p: Problem, profit1: int, profit2: int, sol1: seq<int>, sol2:seq<int>, i: int, j: int) 
                                    // profit1 = profits[i - 1][j - p.weights[i - 1]] 
                                    // profit2 = profits[i - 1][j] 
 requires isValidProblem(p)
 requires 1 <= i <= p.numberOfObjects
 requires 0 <= j <= p.knapsackCapacity
 requires p.weights[i - 1] <= j
 requires isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol1, i - 1, j - p.weights[i - 1])
 requires isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol2, i - 1, j)
 requires computeWeight(p.weights, sol1 + [1], |sol1 + [1]| - 1) <= j
 requires profit1 == gain(p, sol1)
 requires profit2 == gain(p, sol2)
 requires p.gains[i - 1] + profit1 > profit2

 ensures isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, sol1 + [1], i, j)
{
  var s := sol1 + [1];

  if !isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, s, i, j){
    ExistsOptimalPartialSolution(p, i, j);
    //assert exists x :: isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, x, i, j);
    var x : seq<int> :| isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, x, i, j);
    assert gain(p, x) > gain(p, sol1 + [1]);
    if x[i - 1] == 0 {
      assert gain(p, x) <= profit2 by // <= profits[i - 1][j]
      {
        LastElementIs0ForGainHelper(p, x);
        assert gain(p, x[..i - 1]) == gain(p, x);
        LastElementIs0ForWeightHelper(p, x);
        assert weight(p, x) <= j;
        assert weight(p, x[..i - 1]) <= j;
      }
      assert gain(p, sol1 + [1]) > profit2 by // from p.gains[i - 1] + profit1 > profit2, the gain of sol + gain of obj i will be bigger that previous profit
      {
        LastElementIs1ForGainHelper(p, sol1 + [1]);
        assert gain(p, sol1 + [1]) == gain(p, sol1) + p.gains[i - 1];
      }
      assert false; 
    } else {
      AddingObjHasEqualGainAsOptimalSol(p, profit1, profit2, sol1, sol2, x, i, j);
      assert gain(p, x) == gain(p, sol1 + [1]);
    }
  }
}

method getPartialProfits(p: Problem, profits: seq<seq<int>>, solutions : seq<seq<seq<int>>>, i: int) returns (partialProfits: seq<int>, partialSolutions: seq<seq<int>>)
  requires isValidProblem(p)
  requires 0 < i < p.numberOfObjects + 1
  requires i == |profits| == |solutions|
  requires forall k :: 0 <= k < i ==> |profits[k]| == p.knapsackCapacity + 1

  requires forall k :: 0 <= k < i ==> |solutions[k]| == p.knapsackCapacity + 1
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == k
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> hasOnlyPermittedValues(solutions[k][q])
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> 0 <= |solutions[k][q]| <= p.numberOfObjects
  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                    isPartialSolutionOfFirstIObjectsAndWeightJ(p, solutions[k][q], k, q)

  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                    isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, solutions[k][q], k, q) 
  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                gain(p, solutions[k][q]) == profits[k][q]

  ensures |partialSolutions| == p.knapsackCapacity + 1
  ensures |partialProfits| == p.knapsackCapacity + 1
  ensures 0 <= |profits| <= p.numberOfObjects + 1 
  ensures forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == i
  ensures forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
  ensures forall k :: 0 <= k < |partialSolutions| ==> 0 <= |partialSolutions[k]| <= p.numberOfObjects
  ensures forall k :: 0 <= k < |partialSolutions| ==> isPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k) 

  ensures forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k)
  ensures forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]
{
        partialProfits := [];
        var j := 0;
        partialSolutions := [];

        while j <= p.knapsackCapacity
          invariant 0 <= j <= p.knapsackCapacity + 1
          invariant 0 <= |profits| <= p.numberOfObjects + 1
          invariant |partialProfits| == j
          invariant |partialSolutions| == j

          invariant forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
          invariant forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k)
          invariant forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]
        {
          if j == 0 {

              var currentProfit, currentSolution := caseMaximumWeightAllowedIs0(p, profits, partialProfits, partialSolutions, i, j);
              partialProfits := partialProfits + [currentProfit];
              partialSolutions := partialSolutions + [currentSolution];

              assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j);

          } else {
            if p.weights[i - 1] <= j {
              if p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]] > profits[i - 1][j] {

                  var currentProfit, currentSolution := caseObtainingBetterProfit(p, profits, solutions, partialProfits, partialSolutions, i, j);
                  partialProfits := partialProfits + [currentProfit];
                  partialSolutions := partialSolutions + [currentSolution];

                  assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j);

              } else {

                  var currentProfit, currentSolution := caseNotObtainingBetterProfit(p, profits, solutions, partialProfits, partialSolutions, i, j);
                  partialProfits := partialProfits + [currentProfit];
                  partialSolutions := partialSolutions + [currentSolution];

                  assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j);

              }
            } else {

                var currentProfit, currentSolution := caseObjWeightExceedsAllowedCapacity(p, profits, solutions, partialProfits, partialSolutions, i, j);
                partialProfits := partialProfits + [currentProfit];
                partialSolutions := partialSolutions + [currentSolution];

                assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j);

            }
          }
          j := j + 1;
          
        }
}

method caseMaximumWeightAllowedIs0(p: Problem, profits: seq<seq<int>>, partialProfits: seq<int>, partialSolutions: seq<seq<int>>, i: int, j: int) returns (currentProfit: int, currentSolution: seq<int>)
  requires isValidProblem(p)
  requires 0 < i <= p.numberOfObjects
  requires i == |profits|

  requires |partialSolutions| == |partialProfits| == j == 0
  requires forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k) 
  requires forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]

  ensures isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j)
  ensures currentProfit == gain(p, currentSolution)
                
{
    currentProfit := 0;
    currentSolution := seq(i, w => 0);

    assert |currentSolution| == i;
    Weight0Lemma(p, currentSolution, |currentSolution| - 1);
    assert weight(p, currentSolution) == 0 <= j;
    assert isPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j);
    
    MaximumWeightAllowedIs0(p, currentSolution, i, j);
    Weight0ImpliesGain0(p, currentSolution, i, j);
    
    assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j);
}

method caseObtainingBetterProfit(p: Problem, profits: seq<seq<int>>, solutions: seq<seq<seq<int>>>, partialProfits: seq<int>, partialSolutions: seq<seq<int>>, i: int, j: int) returns (currentProfit: int, currentSolution: seq<int>)
  requires isValidProblem(p)
  requires 0 < i <= p.numberOfObjects
  requires i == |profits| == |solutions|
  requires 1 <= j <= p.knapsackCapacity

  requires forall k :: 0 <= k < i ==> |profits[k]| == |solutions[k]| == p.knapsackCapacity + 1
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == k
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> hasOnlyPermittedValues(solutions[k][q])

  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                    isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, solutions[k][q], k, q) 
  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                gain(p, solutions[k][q]) == profits[k][q]

  requires |partialSolutions| == |partialProfits| == j
  requires forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
  requires forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k) 
  requires forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]
  
  requires p.weights[i - 1] <= j
  requires p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]] > profits[i - 1][j]

  ensures isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j)
  ensures currentProfit == gain(p, currentSolution)
                
{
    currentProfit := p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]];
    currentSolution := solutions[i - 1][j - p.weights[i - 1]];
    
    AddingObjectDoesNotExceedsCapacity(p, i - 1, j, currentSolution);
    assert weight(p, currentSolution) <= j;

    CaseTakingObjectLeadsToOptimal(p, profits[i - 1][j - p.weights[i - 1]], profits[i - 1][j], 
      currentSolution, solutions[i - 1][j], i, j);

    currentSolution := currentSolution + [1];
    assert |currentSolution| == i;

    assert currentSolution[..|currentSolution| - 1] == solutions[i - 1][j - p.weights[i - 1]];
    LastElementIs1ForGainHelper(p, currentSolution);
    // assert gain(p, currentSolution) == gain(p, currentSolution[..|currentSolution| - 1]) + p.gains[i - 1] == currentProfit;

    assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j);        
}

method caseNotObtainingBetterProfit(p: Problem, profits: seq<seq<int>>, solutions: seq<seq<seq<int>>>, partialProfits: seq<int>, partialSolutions: seq<seq<int>>, i: int, j: int) returns (currentProfit: int, currentSolution: seq<int>)
  requires isValidProblem(p)
  requires 0 < i <= p.numberOfObjects
  requires i == |profits| == |solutions|
  requires 1 <= j <= p.knapsackCapacity

  requires forall k :: 0 <= k < i ==> |profits[k]| == |solutions[k]| == p.knapsackCapacity + 1
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == k
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> hasOnlyPermittedValues(solutions[k][q])

  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                    isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, solutions[k][q], k, q) 
  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                gain(p, solutions[k][q]) == profits[k][q]

  requires |partialSolutions| == |partialProfits| == j
  requires forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
  requires forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k) 
  requires forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]
  
  requires p.weights[i - 1] <= j
  requires p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]] <= profits[i - 1][j]

  ensures isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j)
  ensures currentProfit == gain(p, currentSolution)
                
{
    currentProfit := profits[i - 1][j];
    currentSolution := solutions[i - 1][j];

    NotAddingObjectDoesNotChangeSolWeight(p, j, currentSolution);
    assert weight(p, currentSolution) <= j;

    NotTakingObjectLeadsToOptimalCase1(p, profits[i - 1][j - p.weights[i - 1]], profits[i - 1][j], 
      solutions[i - 1][j - p.weights[i - 1]], currentSolution, i, j);

    currentSolution := currentSolution + [0];
    assert |currentSolution| == i;
    
    LastElementIs0ForGainHelper(p, currentSolution);

    assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j);   
}

method caseObjWeightExceedsAllowedCapacity(p: Problem, profits: seq<seq<int>>, solutions: seq<seq<seq<int>>>, partialProfits: seq<int>, partialSolutions: seq<seq<int>>, i: int, j: int) returns (currentProfit: int, currentSolution: seq<int>)
  requires isValidProblem(p)
  requires 0 < i <= p.numberOfObjects
  requires i == |profits| == |solutions|
  requires 1 <= j <= p.knapsackCapacity

  requires forall k :: 0 <= k < i ==> |profits[k]| == |solutions[k]| == p.knapsackCapacity + 1
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == k
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> hasOnlyPermittedValues(solutions[k][q])

  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                    isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, solutions[k][q], k, q) 
  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> 
                gain(p, solutions[k][q]) == profits[k][q]

  requires |partialSolutions| == |partialProfits| == j
  requires forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
  requires forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, partialSolutions[k], i, k) 
  requires forall k :: 0 <= k < |partialSolutions| ==> gain(p, partialSolutions[k]) == partialProfits[k]
  requires p.weights[i - 1] > j

  ensures isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j)
  ensures currentProfit == gain(p, currentSolution)
                
{
    currentProfit := profits[i - 1][j];
    currentSolution := solutions[i - 1][j];

    NotAddingObjectDoesNotChangeSolWeight(p, j, currentSolution);
    assert weight(p, currentSolution) <= j;
    assert isPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i - 1, j);

    NotTakingObjectLeadsToOptimalCase2(p, currentSolution, i, j);

    currentSolution := currentSolution + [0];
    assert |currentSolution| == i;
    assert isPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j);
    
    LastElementIs0ForGainHelper(p, currentSolution);

    assert isOptimalPartialSolutionOfFirstIObjectsAndWeightJ(p, currentSolution, i, j);        
}

method Main()
{
    var p: Problem := Problem(numberOfObjects := 4, knapsackCapacity := 8, 
                                    gains := [1, 2, 5, 6], weights := [2, 3, 4, 5]);
    var maximProfit, finalSolution := KnapsackProblem(p);

    print "\n Maximum profit is: ";
    print maximProfit;

    print "\n Optimal solution is: ";
    print finalSolution;
}