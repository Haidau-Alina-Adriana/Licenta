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
  requires isValidPartialSolution(p, solution)
  requires |solution| == p.numberOfObjects
  ensures gain(p, solution) == if |solution| == 0 then 0 else computeGain(p.gains, solution, |solution| - 1)
{
  if |solution| == 0 then 0 else computeGain(p.gains, solution, |solution| - 1)
}

function computeGain(gains: seq<int>, solution: seq<int>, i: int) : int
  requires 0 <= i < |solution|
  requires 0 <= i < |gains|
  requires hasOnlyPermittedValues(solution)
  requires |solution| == |gains|
  ensures computeGain(gains, solution, i) == if i == 0 then solution[0] * gains[0]  else solution[i] * gains[i] + computeGain(gains, solution, i - 1)
{
   if i == 0 then solution[0] * gains[0]  else solution[i] * gains[i] + computeGain(gains, solution, i - 1)
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
  ensures computeWeight(weights, solution, i) == if i == 0 then solution[0] * weights[0]  else solution[i] * weights[i] + computeWeight(weights, solution, i - 1)
{
   if i == 0 then solution[0] * weights[0] else solution[i] * weights[i] + computeWeight(weights, solution, i - 1)
}

predicate isValidSolution(p: Problem, solution: seq<int>)
requires isValidProblem(p)
requires isValidPartialSolution(p, solution)
{
  isPartialSolution(p, solution) 
}

predicate isSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
  requires isValidPartialSolution(p, solution)
{
  isValidSolution(p, solution) &&
  weight(p, solution) <= p.knapsackCapacity
}

predicate isValidPartialSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
{
  |solution| == p.numberOfObjects && 
  hasOnlyPermittedValues(solution)
}

predicate isPartialSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
  requires isValidPartialSolution(p, solution)
{ 
  weight(p, solution) <= p.knapsackCapacity
}

ghost predicate existsPartialSolutionOfProfit(p: Problem, profit: int, dim: int, partWeight: int, partialSolution: seq<int>)
  requires isValidProblem(p)
  requires 0 <= dim <= p.numberOfObjects
  requires 0 <= partWeight <= p.knapsackCapacity
{
  isValidPartialSolution(p, partialSolution) && isPartialSolution(p, partialSolution) 
  && gain(p, partialSolution) == profit && weight(p, partialSolution) <= partWeight && |partialSolution| == p.numberOfObjects
}

// ghost predicate isOptimalSolution(p: Problem, solution: seq<int>)
//   requires isValidProblem(p)
//   requires isValidPartialSolution(p, solution)
//   requires isValidSolution(p, solution)  
// {
//     isSolution(p, solution) &&
//     forall s: seq<int> :: (((isValidSolution(p, s) && isSolution(p, s)) ==> 
//     gain(p, solution) >= gain(p, s)))
// }

method getMaximProfit(p: Problem) returns (maximProfit: int, finalSolution: seq<int>)
  requires isValidProblem(p)
  // ensures isSolution(p, finalSolution)
{
    var profits := []; 
    var solutions := [];
    var i := 0;

    var partialProfits, partialSolutions := FillMatrixForObject0(p, profits, solutions, i);
    i := i + 1; 
    profits := profits + [partialProfits];
    solutions := solutions + [partialSolutions];
    assert forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> weight(p, solutions[k][q]) <= q;

    while i <= p.numberOfObjects 
      invariant |profits| == |solutions| == i > 0
      invariant 0 <= i <= p.numberOfObjects + 1
      invariant forall k :: 0 <= k < i ==> |profits[k]| == p.knapsackCapacity + 1
      invariant 0 <= |profits| <= p.numberOfObjects + 1

      invariant forall k :: 0 <= k < |solutions| ==> |solutions[k]| == p.knapsackCapacity + 1
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == p.numberOfObjects 
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> hasOnlyPermittedValues(solutions[k][q])
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> weight(p, solutions[k][q]) <= q //each solution does not exceed the
                                                                                                      //maximum required capacity between 0 and p.knapsackCapacity
      invariant i < p.numberOfObjects ==> forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> forall w :: |solutions[k][q][..i]| <= w < |solutions[k][q]| ==>
                                                                                                  solutions[k][q][w] == 0
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
    
    finalSolution := solutions[p.numberOfObjects][p.knapsackCapacity];
    assert weight(p, finalSolution) <= p.knapsackCapacity;
    assert isSolution(p, finalSolution);

    maximProfit := profits[p.numberOfObjects][p.knapsackCapacity];
    // TODO optimal solution verification
}


method FillMatrixForObject0(p: Problem, profits: seq<seq<int>>, solutions : seq<seq<seq<int>>>, i: int) returns (partialProfits: seq<int>, partialSolutions: seq<seq<int>>)
  requires isValidProblem(p)
  requires |profits| == |solutions| == i == 0

  ensures |partialProfits| == p.knapsackCapacity + 1
  ensures |partialSolutions| == p.knapsackCapacity + 1
  ensures forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == p.numberOfObjects
  ensures forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
  ensures forall k :: 0 <= k < |partialSolutions| ==> weight(p, partialSolutions[k]) <= k
  ensures forall k :: 0 <= k < |partialSolutions| ==> forall q :: 0 <= q < |partialSolutions[k]| ==> partialSolutions[k][q] == 0
{
        partialProfits := [];
        var j := 0;
        var currentSolution := seq(p.numberOfObjects, k => 0);
        partialSolutions := [];

        Weight0Lemma(p, currentSolution, |currentSolution| - 1);
        assert weight(p, currentSolution) == 0;

         while j <= p.knapsackCapacity
          invariant 0 <= j <= p.knapsackCapacity + 1
          invariant |partialProfits| == j
          invariant |partialSolutions| == j

          invariant |partialSolutions| > 0 ==> forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == p.numberOfObjects 
          invariant forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
          invariant forall k :: 0 <= k < |partialSolutions| ==> weight(p, partialSolutions[k]) <= k
          invariant forall k :: 0 <= k < |partialSolutions| ==> forall q :: 0 <= q < |partialSolutions[k]| ==> partialSolutions[k][q] == 0
        {
              partialProfits := partialProfits + [0];
              currentSolution := seq(p.numberOfObjects, w => 0);
              partialSolutions := partialSolutions + [currentSolution];

              assert |currentSolution| == p.numberOfObjects;
              assert isValidPartialSolution(p, currentSolution);
              Weight0Lemma(p, currentSolution, |currentSolution| - 1);
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
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == p.numberOfObjects 
  requires forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> hasOnlyPermittedValues(solutions[k][q])
  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> weight(p, solutions[k][q]) <= q
  requires forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> forall w :: |solutions[k][q][..i]| <= w < |solutions[k][q]| ==>
                                                                                                  solutions[k][q][w] == 0

  ensures |partialSolutions| == p.knapsackCapacity + 1
  ensures |partialProfits| == p.knapsackCapacity + 1
  ensures 0 <= |profits| <= p.numberOfObjects + 1 
  ensures forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == p.numberOfObjects
  ensures forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
  ensures forall k :: 0 <= k < |partialSolutions| ==> weight(p, partialSolutions[k]) <= k
  ensures forall k :: 0 <= k < |partialSolutions| ==> forall q :: |partialSolutions[k][..i]| <= q < |partialSolutions[k]| ==> partialSolutions[k][q] == 0
{
        partialProfits := [];
        var j := 0;
        var currentSolution := seq(p.numberOfObjects, k => 0);
        partialSolutions := [];

        assert |currentSolution| == p.numberOfObjects;
        assert forall l :: 0 <= l < |currentSolution| ==> currentSolution[l] == 0; 
        Weight0Lemma(p, currentSolution, |currentSolution| - 1);
        assert weight(p, currentSolution) == 0 <= p.knapsackCapacity;
        
        while j <= p.knapsackCapacity
          invariant 0 <= j <= p.knapsackCapacity + 1
          invariant 0 <= |profits| <= p.numberOfObjects + 1
          invariant |partialProfits| == j
          invariant |partialSolutions| == j

          invariant forall k :: 0 <= k < i ==> |solutions[k]| == p.knapsackCapacity + 1
          invariant forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == p.numberOfObjects 
          invariant |partialSolutions| > 0 ==> forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == p.numberOfObjects 

          invariant forall k :: 0 <= k < i ==> forall q :: 0 <= q < |solutions[k]| ==> hasOnlyPermittedValues(solutions[k][q])
          invariant forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])

          invariant |currentSolution| == p.numberOfObjects
          invariant hasOnlyPermittedValues(currentSolution)

          invariant forall k :: |currentSolution[..i]| <= k < |currentSolution| ==> currentSolution[k] == 0 // all objects after the i obj will not be taken in knapsack
          invariant forall k :: 0 <= k < |partialSolutions| ==> forall q :: |partialSolutions[k][..i]| <= q < |partialSolutions[k]| ==> partialSolutions[k][q] == 0
          invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> forall w :: |solutions[k][q][..i]| <= w < |solutions[k][q]| ==>
                                                                                                  solutions[k][q][w] == 0
          invariant forall k :: 0 <= k < |partialSolutions| ==> weight(p, partialSolutions[k]) <= k
          invariant weight(p, currentSolution) <= j
          invariant isPartialSolution(p, currentSolution)
        {
          if j == 0 {
              partialProfits := partialProfits + [0];

              currentSolution := seq(p.numberOfObjects, w => 0);
              partialSolutions := partialSolutions + [currentSolution];

              assert |currentSolution| == p.numberOfObjects;
              assert isValidPartialSolution(p, currentSolution);

              Weight0Lemma(p, currentSolution,|currentSolution| - 1);
              assert weight(p, currentSolution) == 0 <= j;
              assert isValidPartialSolution(p, currentSolution);
              assert isPartialSolution(p, currentSolution);
          } else {
            if p.weights[i - 1] <= j {
              if p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]] > profits[i - 1][j] {
                  partialProfits := partialProfits + [p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]]];

                  var currentSolution := solutions[i - 1][j - p.weights[i - 1]];
                  TookObjIntoKnapsackLemma(p, i - 1, j, currentSolution); // i - 1 obj from getPartialProfits == i obj from solution 

                  currentSolution := currentSolution[i - 1 := 1];
                  partialSolutions := partialSolutions + [currentSolution];

                  assert |currentSolution| == p.numberOfObjects;
                  assert isValidPartialSolution(p, currentSolution);
                  assert weight(p, currentSolution) <= j;
                  assert isPartialSolution(p, currentSolution);
              } else {
                  partialProfits := partialProfits + [profits[i - 1][j]];

                  var currentSolution := solutions[i - 1][j];
                  partialSolutions := partialSolutions + [currentSolution];

                  assert |currentSolution| == p.numberOfObjects;
                  assert isValidPartialSolution(p, currentSolution);
                  assert weight(p, currentSolution) <= j;
                  assert isPartialSolution(p, currentSolution);
              }
            } else {
                partialProfits := partialProfits + [profits[i - 1][j]];

                var currentSolution := solutions[i - 1][j];
                partialSolutions := partialSolutions + [currentSolution];

                assert |currentSolution| == p.numberOfObjects;
                assert isValidPartialSolution(p, currentSolution);
                assert weight(p, currentSolution) <= j;
                assert isPartialSolution(p, currentSolution);
            }
          }
          j := j + 1;
          
        }
}

lemma TookObjIntoKnapsackLemma(p: Problem, i: int, j: int, sol: seq<int>)
  requires isValidProblem(p)
  requires 0 <= i < |sol|
  requires 0 <= i < |p.weights|
  requires |sol| == p.numberOfObjects 
  requires hasOnlyPermittedValues(sol)
  requires 0 <= j <= p.knapsackCapacity + 1

  requires forall k :: |sol[..i + 1]| <= k < |sol| ==> sol[k] == 0 // all objects after i (included) are not taken
  requires weight(p, sol) <= j - p.weights[i]
  
  ensures weight(p, sol[i := 1]) <= j
{                                     //TODO finish lemma
  //  if i == |sol| - 1 {
  //   // assert  computeWeight(p.weights, sol, i) == 0;
  //   assert weight(p, sol) + p.weights[i] <= j;
  // } else {
  //   assert forall k :: |sol[..i + 1]| <= k < |sol| ==> sol[k] == 0;
  //   Weight0Lemma(p, sol[i + 1..], |sol[i + 1..]| - 1);
  //   assert weight(p, sol[i + 1..]) == 0;
  // }
}

// lemma TookObjIntoKnapsackLemma(p: Problem, sol: seq<int>, k: int, i: int, j: int)
//   requires isValidProblem(p)
//   requires 0 <= k < |sol|
//   requires 0 <= k < |p.weights|
//   requires |sol| == p.numberOfObjects 
//   requires hasOnlyPermittedValues(sol)

//   requires 0 <= j <= p.knapsackCapacity + 1
//   requires 1 < i < |sol|
//   // requires p.weights[obj - 1] <= w
//   requires weight(p, sol) == j - p.weights[i - 1]
//   requires sol[i] == 0
//   requires i == |sol| - 1
//   // ensures weight(p, sol[obj - 1 := 1]) == w
// {
//     assert weight(p, sol) <= j;
//     assert weight(p, sol) == computeWeight(p.weights, sol, |sol| - 1);
//     assert computeWeight(p.weights, sol, |sol| - 1) == if |sol| == 1 then sol[0] * p.weights[0] else sol[|sol| - 1] * p.weights[|sol| - 1] + computeWeight(p.weights, sol, |sol| - 2);
//     assert computeWeight(p.weights, sol, |sol| - 1) == if |sol| == 1 then 0 * p.weights[0] else 0 * p.weights[|sol| - 1] + computeWeight(p.weights, sol, |sol| - 2);

//     // cw(p, sol, |sol[..i - 1]| - 1);

//     assert weight(p, sol[..i - 1]) == computeWeight(p.weights, sol[..i - 1], |sol[..i - 1]| - 1);
//     assert computeWeight(p.weights, sol[..i - 1], |sol[..i - 1]| - 1) == if |sol[..i - 1]| == 1 then sol[0] * p.weights[0] else sol[|sol[..i - 1]| - 1] * p.weights[|sol[..i - 1]| - 1] + computeWeight(p.weights, sol[..i - 1], |sol[..i - 1]| - 2);
//     // assert computeWeight(p.weights, sol[..i - 1], |sol[..i - 1]| - 1) == if |sol[..i - 1]| == 1 then 0 * p.weights[0] else 0 * p.weights[|sol[..i - 1]| - 1] + computeWeight(p.weights, sol[..i - 1], |sol[..i - 1]| - 2);
    
//     // assert weight(p, sol) == weight(p, sol[..obj - 1]);
//     // assert p.weights[obj - 1] <= w;
//     // assert weight(p, sol[obj - 1 := 1]) <= w;
// }

lemma cw(p: Problem, sol: seq<int>, i: int)
  requires hasOnlyPermittedValues(sol)
  requires 0 < i < |p.weights|
  requires |sol| == |p.weights|
  requires 0 < i < |sol| - 1
  ensures computeWeight(p.weights, sol, i) == computeWeight(p.weights, sol[..|sol| - 1], i)
{

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

lemma gainLemma(p: Problem, sol: seq<int>, partialProfit: int)
  requires isValidProblem(p)
  // requires isValidPartialSolution(p, sol)
  requires |sol| <= |p.gains| 
  requires |sol| <= |p.weights|
  // ensures gain(p, sol) == partialProfit
{

}

method Main()
{
    var p: Problem := Problem(numberOfObjects := 4, knapsackCapacity := 8, 
                                    gains := [1, 2, 5, 6], weights := [2, 3, 4, 5]);
    var maximProfit, finalSolution := getMaximProfit(p);

    print "\n Profit is: ";
    print maximProfit;

    print "\n Solution is: ";
    print finalSolution;
}