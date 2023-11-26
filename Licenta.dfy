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
  ensures computeGain(gains, solution, i) == if i == 0 then 0 else solution[i] * gains[i] + computeGain(gains, solution, i - 1)
{
   if i == 0 then 0 else solution[i] * gains[i] + computeGain(gains, solution, i - 1)
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
  ensures computeWeight(weights, solution, i) == if i == 0 then 0 else solution[i] * weights[i] + computeWeight(weights, solution, i - 1)
{
   if i == 0 then 0 else solution[i] * weights[i] + computeWeight(weights, solution, i - 1)
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

method getMaximProfit(p: Problem) 
  requires isValidProblem(p)
  // ensures isSolution(p, solution)
  // ensures isValidPartialSolution(p, solution)
{
    var profits := []; 
    var solutions := [];
    var maximProfit := 0;

    var i := 0;

    var partialProfits, partialSolutions := FillMatrixForObject0(p, profits, solutions, i);
    i := i + 1; 
    profits := profits + [partialProfits];
    solutions := solutions + [partialSolutions];
    assert forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> weight(p, solutions[k][q]) <= p.knapsackCapacity;

    while i <= p.numberOfObjects 
      invariant |profits| == |solutions| == i > 0
      invariant 0 <= i <= p.numberOfObjects + 1
      invariant forall k :: 0 <= k < i ==> |profits[k]| == p.knapsackCapacity + 1
      invariant 0 <= |profits| <= p.numberOfObjects + 1

      invariant forall k :: 0 <= k < |solutions| ==> |solutions[k]| == p.knapsackCapacity + 1
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> |solutions[k][q]| == p.numberOfObjects 
      invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> hasOnlyPermittedValues(solutions[k][q])
      // invariant forall k :: 0 <= k < |solutions| ==> forall q :: 0 <= q < |solutions[k]| ==> weight(p, solutions[k][q]) <= p.knapsackCapacity

      // invariant forall x :: 0 <= x < i ==> forall y :: 0 <= y <= p.knapsackCapacity ==> 
      //   existsPartialSolutionOfProfit(p, profits[x][y], x, y, solutions[x][y])
    {
        partialProfits, partialSolutions := getPartialProfits(p, profits, solutions, i);
        profits := profits + [partialProfits];
        solutions := solutions + [partialSolutions];
        i := i + 1; 
    }
    
    maximProfit := profits[p.numberOfObjects][p.knapsackCapacity];
    print maximProfit;
    print "\n";

    for i: int := 0 to |solutions|
    { 
      print solutions[i];
      print "\n";
    }
}


method FillMatrixForObject0(p: Problem, profits: seq<seq<int>>, solutions : seq<seq<seq<int>>>, i: int) returns (partialProfits: seq<int>, partialSolutions: seq<seq<int>>)
  requires isValidProblem(p)
  requires |profits| == |solutions| == i == 0

  ensures |partialProfits| == p.knapsackCapacity + 1
  ensures |partialSolutions| == p.knapsackCapacity + 1
  ensures forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == p.numberOfObjects
  ensures forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
  ensures forall k :: 0 <= k < |partialSolutions| ==> weight(p, partialSolutions[k]) <= p.knapsackCapacity
{
        partialProfits := [];
        var j := 0;
        var currentSolution := seq(p.numberOfObjects, k => 0);
        partialSolutions := [];

        Weight0Lemma(p, currentSolution,|currentSolution| - 1);
        assert weight(p, currentSolution) <= p.knapsackCapacity;

         while j <= p.knapsackCapacity
          invariant 0 <= j <= p.knapsackCapacity + 1
          invariant |partialProfits| == j
          invariant |partialSolutions| == j

          invariant |partialSolutions| > 0 ==> forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == p.numberOfObjects 
          invariant forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
          invariant forall k :: 0 <= k < |partialSolutions| ==> weight(p, partialSolutions[k]) <= p.knapsackCapacity
        {
              partialProfits := partialProfits + [0];
              currentSolution := seq(p.numberOfObjects, w => 0);
              partialSolutions := partialSolutions + [currentSolution];

              assert |currentSolution| == p.numberOfObjects;
              assert isValidPartialSolution(p, currentSolution);
              Weight0Lemma(p, currentSolution,|currentSolution| - 1);
              assert weight(p, currentSolution) <= p.knapsackCapacity;

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

  // requires forall x :: 0 <= x < i - 1 ==> forall y :: 0 <= y <= p.knapsackCapacity ==> 
  //       existsPartialSolutionOfProfit(p, profits[x][y], x, y, solutions[x][y])

  ensures |partialSolutions| == p.knapsackCapacity + 1
  ensures |partialProfits| == p.knapsackCapacity + 1
  ensures 0 <= |profits| <= p.numberOfObjects + 1 
  ensures forall k :: 0 <= k < |partialSolutions| ==> |partialSolutions[k]| == p.numberOfObjects
  ensures forall k :: 0 <= k < |partialSolutions| ==> hasOnlyPermittedValues(partialSolutions[k])
  // ensures forall y :: 0 <= y < |partialProfits| ==>
  //          (existsPartialSolutionOfProfit(p, partialProfits[y], i, y, partialSolutions[y]))
{
        partialProfits := [];
        var j := 0;
        var currentSolution := seq(p.numberOfObjects, k => 0);
        partialSolutions := [];

        assert |currentSolution| == p.numberOfObjects;
        assert forall l :: 0 <= l < |currentSolution| ==> currentSolution[l] == 0; 
        Weight0Lemma(p, currentSolution, |currentSolution| - 1);
        assert weight(p, currentSolution) <= p.knapsackCapacity;
        
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

          // invariant forall y :: 0 <= y < |partialProfits| ==>
          //  (existsPartialSolutionOfProfit(p, partialProfits[y], i, y, partialSolutions[y]))
        {
          if j == 0 {
              partialProfits := partialProfits + [0];

              currentSolution := seq(p.numberOfObjects, w => 0);
              partialSolutions := partialSolutions + [currentSolution];

              assert |currentSolution| == p.numberOfObjects;
              assert isValidPartialSolution(p, currentSolution);

              Weight0Lemma(p, currentSolution,|currentSolution| - 1);
              assert weight(p, currentSolution) <= p.knapsackCapacity;
          } else {
            if p.weights[i - 1] <= j {
              if p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]] > profits[i - 1][j] {
                partialProfits := partialProfits + [p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]]];

                var currentSolution := solutions[i - 1][j - p.weights[i - 1]];                
                currentSolution := currentSolution[i - 1 := 1];
                
                assert p.weights[i - 1] <= j;
                WeightBiggerThan0Lemma(p, currentSolution, |currentSolution| - 1, i, j);
                assert weight(p, currentSolution) <= j;

                partialSolutions := partialSolutions + [currentSolution];

                assert |currentSolution| == p.numberOfObjects;
                assert isValidPartialSolution(p, currentSolution);
              } else {
                partialProfits := partialProfits + [profits[i - 1][j]];

                var currentSolution := solutions[i - 1][j];
                partialSolutions := partialSolutions + [currentSolution];

                assert |currentSolution| == p.numberOfObjects;
                assert isValidPartialSolution(p, currentSolution);
              }
            } else {
              partialProfits := partialProfits + [profits[i - 1][j]];

              var currentSolution := solutions[i - 1][j];
              partialSolutions := partialSolutions + [currentSolution];

              assert |currentSolution| == p.numberOfObjects;
              assert isValidPartialSolution(p, currentSolution);
            }
          }
          j := j + 1;
          
        }
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

lemma WeightBiggerThan0Lemma(p: Problem, sol: seq<int>, i: int, obj: int, w: int)
  requires isValidProblem(p)
  requires 0 <= i < |sol|
  requires 0 <= i < |p.weights|
  requires 0 <= |sol| <= p.numberOfObjects 
  requires hasOnlyPermittedValues(sol)

  requires 0 <= w <= p.knapsackCapacity + 1
  requires 0 < obj < |p.weights| + 1
  requires p.weights[obj - 1] <= w

  ensures computeWeight(p.weights, sol, i) <= w
{
    if i == 0 {
    assert computeWeight(p.weights, sol, i) == 0 <= w;
  } else {
    WeightBiggerThan0Lemma(p, sol, i - 1, obj, w);
    // assert computeWeight(p.weights, sol, i - 1) <= p.knapsackCapacity;
    assert computeWeight(p.weights, sol, i) <= w;
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

// method getPartialSolution(p: Problem, profits: seq<seq<int>>) returns (solution: seq<int>)
//     requires isValidProblem(p)
//     requires 1 <= |profits| <= |p.weights| + 1
//     requires 1 <= |profits| <= p.numberOfObjects + 1
//     requires forall k :: 0 <= k < |profits| ==> 1 <= |profits[k]| <= p.knapsackCapacity + 1
//     requires |profits| > 1 ==> forall a :: 0 <= a < |profits| - 1 ==> |profits[a]| == p.knapsackCapacity + 1
//     ensures hasOnlyPermittedValues(solution)
//     ensures |solution| == p.numberOfObjects
// {
//     solution := [];

//     var i := |profits| - 1;
//     var j := |profits[i]| - 1;

//     var lengthSol := |solution|;
//     var lengthI := i;

//     while i > 0 && j > 0
//       invariant 0 <= i <= |profits| - 1
//       invariant 0 <= i <= |p.weights|
//       invariant 0 <= j <= |profits[i]| - 1
//       invariant 0 <= j <= p.knapsackCapacity + 1
//       invariant hasOnlyPermittedValues(solution)
//       invariant 0 <= i <= p.numberOfObjects
//       invariant |solution| > 0 ==> lengthSol + 1 == |solution|
//       invariant |solution| > 0 ==> lengthI - 1 == i
//       invariant i + |solution| <= p.numberOfObjects 
//       invariant |profits| <= p.numberOfObjects + 1 ==> i <= p.numberOfObjects 
//       invariant i == 0 ==> |solution| <= p.numberOfObjects
//       invariant 0 <= |solution| <= p.numberOfObjects
//       decreases i
//       decreases j
//     {
//       lengthSol := |solution|;
//       lengthI := i;
//       assert 0 <= i - 1 <= |profits| - 1;
//       if profits[i][j] == profits[i - 1][j] {
//         solution := [0] + solution;
//         i := i - 1;
//       } else { 
//         solution := [1] + solution;
//         i := i - 1;
//         if j - p.weights[i] >= 0 {
//           j := j - p.weights[i];
//         }
//       } 
//       assert i >= 0 && i <= |profits| - 1;
//       assert i <= p.numberOfObjects; 
//       assert lengthSol + 1 == |solution|; 
//       assert |solution| >= 0;
//       assert lengthI - 1 == i;

//       assert 0 <= |solution| <= p.numberOfObjects;
//     }  

//     while j == 0 && i > 0 
//       invariant hasOnlyPermittedValues(solution)
//       invariant i + |solution| <= p.numberOfObjects 
//       decreases i
//     {
//       solution := [0] + solution;
//       i := i - 1;
//     }
//     assert 0 <= |solution| <= p.numberOfObjects;

//     i := p.numberOfObjects - |solution|;
//     while i > 0 && |solution| < p.numberOfObjects
//       invariant hasOnlyPermittedValues(solution)
//       invariant |solution| == p.numberOfObjects - i
//       invariant 0 <= i
//       invariant i == 0 ==> |solution| == p.numberOfObjects
//       decreases i
//     {
//       solution := solution + [0];
//       i := i - 1;
//     }
//     assert i == 0;
//     assert |solution| == p.numberOfObjects;
// }

method Main()
{
    var p: Problem := Problem(numberOfObjects := 4, knapsackCapacity := 8, 
                                    gains := [1, 2, 5, 6], weights := [2, 3, 4, 5]);
    getMaximProfit(p);
}