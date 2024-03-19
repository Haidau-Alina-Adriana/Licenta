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

function weight(p: Problem, solution: seq<int>): int
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(solution)
  requires 0 <= |solution| <= p.numberOfObjects
  ensures weight(p, solution) == if |solution| == 0 then 0 else computeWeight(p.weights, solution, |solution| - 1)
{
  if |solution| == 0 then 0 else computeWeight(p.weights, solution, |solution| - 1)
}

function computeWeight(weights: seq<int>, solution: seq<int>, i: int) : int
  requires 0 <= i < |solution|
  requires 0 <= i < |weights|
  requires hasOnlyPermittedValues(solution)
  requires 0 <= |solution| <= |weights|
  ensures computeWeight(weights, solution, i) == if i == 0 then solution[0] * weights[0] else solution[i] * weights[i] + computeWeight(weights, solution, i - 1)
{
   if i == 0 then solution[0] * weights[0] else solution[i] * weights[i] + computeWeight(weights, solution, i - 1)
}

predicate isValidPartialSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
{
  hasOnlyPermittedValues(solution)
}

predicate isPartialSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
{ 
  isValidPartialSolution(p, solution) && 0 <= |solution| <= p.numberOfObjects
  && weight(p, solution) <= p.knapsackCapacity
}

predicate isSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
{
  isValidPartialSolution(p, solution) && |solution| == p.numberOfObjects &&
  weight(p, solution) <= p.knapsackCapacity
}

ghost predicate isOptimalSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
  requires isValidPartialSolution(p, solution)
{
    isOptimalPartialSolution(p, solution) &&
    forall s: seq<int> :: (((isOptimalPartialSolution(p, s)) ==> 
    gain(p, solution) >= gain(p, s)))
}

ghost predicate isOptimalPartialSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
{
    isPartialSolution(p, solution) &&
    forall s: seq<int> :: ((isPartialSolution(p, s) && |s| == |solution| ==> 
    gain(p, solution) >= gain(p, s)))
}

ghost predicate isOptimalPartialSolutionWeigthJ(p: Problem, solution: seq<int>, j: int)
  requires isValidProblem(p)
  requires isPartialSolution(p, solution)
  requires weight(p, solution) <= j
{
    isPartialSolution(p, solution) &&
    forall s: seq<int> :: ((isPartialSolution(p, s) && |s| == |solution| && weight(p, s) <= j ==> 
    gain(p, solution) >= gain(p, s)))
}

lemma TookObjIntoKnapsackLemma(p: Problem, i: int, j: int, sol: seq<int>)  
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

lemma ObjNotTakenIntoKnapsackLemma(p: Problem, j: int, sol: seq<int>)
  requires isValidProblem(p)
  requires hasOnlyPermittedValues(sol)
  requires 0 <= |sol| < p.numberOfObjects

  requires weight(p, sol) <= j
  ensures computeWeight(p.weights, sol + [0], |sol + [0]| - 1) <= j 
{  
  var newSol := sol + [0];
  assert sol == newSol[..|newSol| - 1];

  for a := 0 to |newSol[..|newSol| - 1]|
    invariant 0 <= a <= |newSol[..|newSol| - 1]| + 1
    invariant forall k :: 0 <= k < a ==> computeWeight(p.weights, sol, k) == computeWeight(p.weights, newSol, k)
  {
    assert computeWeight(p.weights, sol, a) == computeWeight(p.weights, newSol, a);
  }
  // if |sol| == 0 {
  //   assert weight(p, sol) <= j;
  // } else {
  //   var newSol := sol + [0];
  //   assert newSol[..|newSol| - 1] == sol;
  //   ObjNotTakenHelper(p, newSol, |newSol| - 2);
  //   assert computeWeight(p.weights, sol + [0], |sol + [0]| - 1) <= j;
  // }
}

// lemma ObjNotTakenHelper(p: Problem, sol: seq<int>, i: int)
//   requires isValidProblem(p)
//   requires hasOnlyPermittedValues(sol)

//   requires 0 <= i < |sol| - 1
//   requires 0 <= i < |p.weights|
//   requires 0 <= |sol| <= |p.weights|
//   requires sol[|sol| - 1] == 0
//   ensures computeWeight(p.weights, sol, i) == computeWeight(p.weights, sol[..|sol| - 1], i)
// {

// }

lemma emptySolutionOptimal(p: Problem, sol: seq<int>)
 requires isValidProblem(p)
 requires isPartialSolution(p, sol)
 requires |sol| == 0

 ensures isOptimalPartialSolution(p, sol)
{
  forall s: seq<int>  | isPartialSolution(p, s) && |sol| == |s|
  ensures gain(p, sol) >= gain(p, s) 
  {

  } 
  assert forall s: seq<int> :: ((isPartialSolution(p, s) && |s| == |sol| ==> gain(p, sol) >= gain(p, s)));
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

lemma MaximumWeightAllowedIs0(p: Problem, sol: seq<int>, i: int)
 requires isValidProblem(p)
 requires isPartialSolution(p, sol)
 requires forall k :: 0 <= k < |sol| ==> sol[k] == 0
 requires |sol| == i
 requires weight(p, sol) == 0

 ensures isOptimalPartialSolution(p, sol)
{
  forall s: seq<int> | isPartialSolution(p, s) && |sol| == |s|
   ensures gain(p, sol) >= gain(p, s) 
  {
    assert gain(p, sol) >= gain(p, s); 
  } 
}

method KnapsackProblem(p: Problem) returns (profit: int, solution: seq<int>)
  requires isValidProblem(p)
  ensures isSolution(p, solution)
  // ensures isOptimalSolution(p, solution)
{
    var profits := []; 
    var solutions := [];
    var i := 0;

    var partialProfits, partialSolutions := FillMatrixForObject0(p, profits, solutions, i);
    profits := profits + [partialProfits];
    solutions := solutions + [partialSolutions];
    assert forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> weight(p, solutions[k][q]) <= q;
    assert forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == i;
    assert forall k :: 0 <= k < |partialSolutions| ==> isPartialSolution(p, partialSolutions[k]);

    assert forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolution(p, partialSolutions[k]);

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
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> weight(p, solutions[k][q]) <= q //each solution does not exceed the
                                                                                                      //maximum required capacity between 0 and p.knapsackCapacity
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> weight(p, solutions[k][q]) <= p.knapsackCapacity
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> isPartialSolution(p, solutions[k][q])

      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> isOptimalPartialSolution(p, solutions[k][q])
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
    assert isSolution(p, solution);

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
  ensures forall k :: 0 <= k < |partialSolutions| ==> isPartialSolution(p, partialSolutions[k])

  ensures forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolution(p, partialSolutions[k])
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
          invariant forall k :: 0 <= k < |partialSolutions| ==> isPartialSolution(p, partialSolutions[k])

          invariant forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolution(p, partialSolutions[k])
        {
              partialProfits := partialProfits + [0];
              currentSolution := [];
              emptySolutionOptimal(p, currentSolution);
              assert isOptimalPartialSolution(p, currentSolution);
              partialSolutions := partialSolutions + [currentSolution];

              assert |currentSolution| == i;
              assert weight(p, currentSolution) <= j;

              j := j + 1;
        }
}

method getPartialProfits(p: Problem, profits: seq<seq<int>>, solutions : seq<seq<seq<int>>>, i: int) returns (partialProfits: seq<int>, partialSolutions: seq<seq<int>>)
  requires isValidProblem(p)
  requires 0 < i < p.numberOfObjects + 1
  requires |profits| == i
  requires forall k :: 0 <= k < i ==> |profits[k]| == p.knapsackCapacity + 1

  requires |solutions| == i
  requires forall k :: 0 <= k < i ==> |solutions[k]| == p.knapsackCapacity + 1
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == k
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> hasOnlyPermittedValues(solutions[k][q])
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> 0 <= |solutions[k][q]| <= p.numberOfObjects
  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> weight(p, solutions[k][q]) <= q
  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> weight(p, solutions[k][q]) <= p.knapsackCapacity

  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> isOptimalPartialSolution(p, solutions[k][q]) 

  ensures |partialSolutions| == p.knapsackCapacity + 1
  ensures |partialProfits| == p.knapsackCapacity + 1
  ensures 0 <= |profits| <= p.numberOfObjects + 1 
  ensures forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == i
  ensures forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
  ensures forall k :: 0 <= k < |partialSolutions| ==> 0 <= |partialSolutions[k]| <= p.numberOfObjects
  ensures forall k :: 0 <= k < |partialSolutions| ==> weight(p, partialSolutions[k]) <= k
  ensures forall k :: 0 <= k < |partialSolutions| ==> weight(p, partialSolutions[k]) <= p.knapsackCapacity
  ensures forall k :: 0 <= k < |partialSolutions| ==> isPartialSolution(p, partialSolutions[k]) 

  ensures forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolution(p, partialSolutions[k])
{
        partialProfits := [];
        var j := 0;
        var currentSolution := seq(i, k => 0);
        partialSolutions := [];

        assert |currentSolution| == i;
        assert forall l :: 0 <= l < |currentSolution| ==> currentSolution[l] == 0; 
        Weight0Lemma(p, currentSolution, |currentSolution| - 1);
        assert weight(p, currentSolution) == 0 <= p.knapsackCapacity;

        MaximumWeightAllowedIs0(p, currentSolution, i);
        // assume false; 
        assert isOptimalPartialSolution(p, currentSolution);
        assume false; 

        while j <= p.knapsackCapacity
          invariant 0 <= j <= p.knapsackCapacity + 1
          invariant 0 <= |profits| <= p.numberOfObjects + 1
          invariant |partialProfits| == j
          invariant |partialSolutions| == j

          invariant forall k :: 0 <= k < i ==> |solutions[k]| == p.knapsackCapacity + 1
          invariant forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == k
          invariant forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> 0 <= |solutions[k][q]| <= p.numberOfObjects

          invariant |partialSolutions| > 0 ==> forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == i
          invariant forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
          invariant forall k :: 0 <= k < |partialSolutions| ==> 0 <= |partialSolutions[k]| <= p.numberOfObjects

          invariant |currentSolution| == i
          invariant hasOnlyPermittedValues(currentSolution)

          invariant forall k :: 0 <= k < |partialSolutions| ==> weight(p, partialSolutions[k]) <= k
          invariant weight(p, currentSolution) <= j
          invariant isPartialSolution(p, currentSolution)

          invariant forall k :: 0 <= k < |partialSolutions| ==> isOptimalPartialSolution(p, partialSolutions[k])
          invariant isOptimalPartialSolution(p, currentSolution)
        {
          if j == 0 {
              partialProfits := partialProfits + [0];
              currentSolution := seq(i, w => 0);
              partialSolutions := partialSolutions + [currentSolution];

              assert |currentSolution| == i;
              Weight0Lemma(p, currentSolution,|currentSolution| - 1);
              assert weight(p, currentSolution) == 0 <= j;
              assert isPartialSolution(p, currentSolution);

              assume isOptimalPartialSolution(p, currentSolution);

          } else {
            if p.weights[i - 1] <= j {
              if p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]] > profits[i - 1][j] {
                  partialProfits := partialProfits + [p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]]];
                  var currentSolution := solutions[i - 1][j - p.weights[i - 1]];

                  TookObjIntoKnapsackLemma(p, i - 1, j, currentSolution);
                  assert weight(p, currentSolution) <= j;

                  currentSolution := currentSolution + [1];
                  partialSolutions := partialSolutions + [currentSolution];

                  assert |currentSolution| == i;
                  assert isPartialSolution(p, currentSolution);

                  assume isOptimalPartialSolution(p, currentSolution);
              } else {
                  partialProfits := partialProfits + [profits[i - 1][j]];
                  var currentSolution := solutions[i - 1][j];
                  assert weight(p, solutions[i - 1][j]) <= j;

                  ObjNotTakenIntoKnapsackLemma(p, j, currentSolution);

                  currentSolution := currentSolution + [0];
                  partialSolutions := partialSolutions + [currentSolution];

                  assert |currentSolution| == i;
                  assert weight(p, currentSolution) <= j;
                  assert isPartialSolution(p, currentSolution);

                  assume isOptimalPartialSolution(p, currentSolution);
              }
            } else {
                partialProfits := partialProfits + [profits[i - 1][j]];
                var currentSolution := solutions[i - 1][j];

                ObjNotTakenIntoKnapsackLemma(p, j, currentSolution);
                
                currentSolution := currentSolution + [0];
                partialSolutions := partialSolutions + [currentSolution];

                assert |currentSolution| == i;
                assert weight(p, currentSolution) <= j;

                assume isOptimalPartialSolution(p, currentSolution);
            }
          }
          j := j + 1;
          
        }
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