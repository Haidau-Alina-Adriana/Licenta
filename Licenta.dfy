datatype Problem = Problem(numberOfObjects: int, knapsackCapacity: int, gains: seq<int>, weights: seq<int>)

predicate hasPositiveValues(input: seq<int>)
{
    forall i :: 0 <= i < |input| ==> input[i] > 0
}

predicate hasOnlyPermittedValues(solution: seq<int>)
{
  forall k :: 0 <= k < |solution| ==> solution[k] == 0 || solution[k] == 1
}

predicate isValidProblem(problem: Problem)
{
    |problem.gains| == |problem.weights| == problem.numberOfObjects && 
    problem.numberOfObjects > 0 && problem.knapsackCapacity >= 0 && 
    hasPositiveValues(problem.gains) && hasPositiveValues(problem.weights) 
}

function max(p1: int, p2: int): int
{
    if p1 > p2 then p1 else p2
}

function gain(problem: Problem, solution: seq<int>): int
  requires isValidProblem(problem)
  requires hasOnlyPermittedValues(solution)
  requires isValidPartialSolution(problem, solution)
  requires 0 <= |solution| <= problem.numberOfObjects
  ensures gain(problem, solution) == if |solution| == 0 then 0 else computeGain(problem.gains, solution, |solution| - 1)
  // ensures if (forall j :: 0 <= j < |solution| ==> solution[j] == 0) then gain(problem, solution) == 0 else true
{
  if |solution| == 0 then 0 else computeGain(problem.gains, solution, |solution| - 1)
}

function computeGain(gains: seq<int>, solution: seq<int>, i: int) : int
  requires 0 <= i < |solution|
  requires 0 <= i < |gains|
  requires hasOnlyPermittedValues(solution)
  requires 0 <= |solution| <= |gains|
  ensures computeGain(gains, solution, i) == if i == 0 then 0 else solution[i] * gains[i] + computeGain(gains, solution, i - 1)
  // ensures if (forall j :: 0 <= j < |solution| ==> solution[j] == 0) then computeGain(gains, solution, i) == 0 else true
{
   if i == 0 then 0 else solution[i] * gains[i] + computeGain(gains, solution, i - 1)
}

function weight(problem: Problem, solution: seq<int>): int
  requires isValidProblem(problem)
  requires hasOnlyPermittedValues(solution)
  requires 0 <= |solution| <= problem.numberOfObjects
  ensures weight(problem, solution) == if |solution| == 0 then 0 else computeWeight(problem.weights, solution, |solution| - 1)
  // ensures if (forall j :: 0 <= j < |solution| ==> solution[j] == 0) then weight(problem, solution) == 0 else true
{
  if |solution| == 0 then 0 else computeWeight(problem.weights, solution, |solution| - 1)
}

function computeWeight(weights: seq<int>, solution: seq<int>, i: int) : int
  requires 0 <= i < |solution|
  requires 0 <= i < |weights|
  requires hasOnlyPermittedValues(solution)
  requires 0 <= |solution| <= |weights|
  ensures computeWeight(weights, solution, i) == if i == 0 then 0 else solution[i] * weights[i] + computeWeight(weights, solution, i - 1)
  // ensures if (forall j :: 0 <= j < |solution| ==> solution[j] == 0) then computeWeight(weights, solution, i) == 0 else true
{
   if i == 0 then 0 else solution[i] * weights[i] + computeWeight(weights, solution, i - 1)
}

predicate isValidSolution(problem: Problem, solution: seq<int>)
requires isValidProblem(problem)
requires isValidPartialSolution(problem, solution)
{
  isPartialSolution(problem, solution) &&
  |solution| == problem.numberOfObjects
}

predicate isSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
  requires isValidPartialSolution(p, solution)
{
  isValidSolution(p, solution) &&
  weight(p, solution) <= p.knapsackCapacity
}

predicate isValidPartialSolution(problem: Problem, solution: seq<int>)
  requires isValidProblem(problem)
//conditie ca suma obiectelor mai mica decat cap rucsacului
{
  0 <= |solution| <= problem.numberOfObjects && hasOnlyPermittedValues(solution)
}

predicate isPartialSolution(problem: Problem, solution: seq<int>)
  requires isValidProblem(problem)
  requires isValidPartialSolution(problem, solution)
{ 
  weight(problem, solution) <= problem.knapsackCapacity
}

ghost predicate existsPartialSolutionOfProfit(p: Problem, profit: int, dim: int, partWeight: int)
  requires isValidProblem(p)
  requires 0 <= dim <= p.numberOfObjects
  requires 0 <= partWeight <= p.knapsackCapacity
{
  exists sol : seq<int> :: (isValidPartialSolution(p, sol) && isPartialSolution(p, sol) 
  && gain(p, sol) == profit && weight(p, sol) <= partWeight && |sol| == dim)
}

// ghost predicate isOptimalSolution(problem: Problem, solution: seq<int>)
//   requires isValidProblem(problem)
//   requires isValidPartialSolution(problem, solution)
//   requires isValidSolution(problem, solution)  
// {
//     isSolution(problem, solution) &&
//     forall s: seq<int> :: (((isValidSolution(problem, s) && isSolution(problem, s)) ==> 
//     gain(problem, solution) >= gain(problem, s)))
// }

method addSequence(existingSeq: seq<seq<int>>, newSeq: seq<int>, c: int) returns (result: seq<seq<int>>)
  requires |newSeq| == c
  ensures result == existingSeq + [newSeq]
  ensures |result| == |existingSeq| + 1
{
  result := existingSeq + [newSeq];
}

method getMaximProfit(p: Problem) 
  requires isValidProblem(p)
  // ensures isSolution(p, solution)
  // ensures isValidPartialSolution(p, solution)
{
    var profits := []; 
    var partialSolutions := [];
    var maximProfit := 0;

    var i := 0;
    while i <= p.numberOfObjects 
      invariant |profits| == i
      invariant 0 <= i <= p.numberOfObjects + 1
      invariant forall k :: 0 <= k < i ==> |profits[k]| == p.knapsackCapacity + 1
      invariant 0 <= |profits| <= p.numberOfObjects + 1
      invariant forall x :: 0 <= x < i ==> forall y :: 0 <= y <= p.knapsackCapacity ==> 
        existsPartialSolutionOfProfit(p, profits[x][y], x, y)
    {
        var partialProfits := getPartialProfits(p, profits, partialSolutions, i);
        profits := addSequence(profits, partialProfits, p.knapsackCapacity + 1);
        i := i + 1; 
    }
    
    maximProfit := profits[p.numberOfObjects][p.knapsackCapacity];
    // solution := getKnapsackObjects(p, profits);
}

method getPartialProfits(p: Problem, profits: seq<seq<int>>, partialSolutions : seq<seq<seq<int>>>,i: int) returns (partialProfits: seq<int>)
  requires isValidProblem(p)
  requires |profits| == i
  requires 0 <= i < p.numberOfObjects + 1
  requires 0 <= |profits| <= p.numberOfObjects + 1
  requires forall k :: 0 <= k < i ==> |profits[k]| == p.knapsackCapacity + 1

  requires forall x :: 0 <= x < i - 1 ==> forall y :: 0 <= y <= p.knapsackCapacity ==> 
        existsPartialSolutionOfProfit(p, profits[x][y], x, y)

  ensures |partialProfits| == p.knapsackCapacity + 1
  ensures 0 <= |profits| <= p.numberOfObjects + 1 
  ensures forall y :: 0 <= y < |partialProfits| ==>
           (existsPartialSolutionOfProfit(p, partialProfits[y], i, y))
{
        partialProfits := [];
        var j := 0;
        var partialSolution := [];

        while j <= p.knapsackCapacity
          invariant 0 <= j <= p.knapsackCapacity + 1
          invariant 0 <= |profits| <= p.numberOfObjects + 1
          invariant |partialProfits| == j
          invariant forall y :: 0 <= y < |partialProfits| ==>
           (existsPartialSolutionOfProfit(p, partialProfits[y], i, y))
        {
          if i == 0 || j == 0 {
              partialProfits := partialProfits + [0];
              partialSolution := seq(p.numberOfObjects, w => 0);
          } else {
            if p.weights[i - 1] <= j {
              partialProfits := partialProfits + [max(p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]], profits[i - 1][j])];
            } else {
              partialProfits := partialProfits + [profits[i - 1][j]];
            }
          }
          // partialSolutions := partialSolutions + [partialSolution];
          j := j + 1;
        }
}

lemma isPartialSolutionLemma(p: Problem, sol: seq<int>)
  requires isValidProblem(p)
  // requires isValidPartialSolution(p, sol)
  requires forall i :: 0 <= i < |sol| ==> sol[i] == 0
  requires |sol| <= |p.gains| 
  requires |sol| <= |p.weights|
  // ensures weight(p, sol) <= p.knapsackCapacity
{
  // if |sol| == 0 {
  //   assert weight(p, sol) == 0 <= p.knapsackCapacity;
  //   // assert computeWeight(p.weights, sol, |sol|) == if |sol| - 1 == 0 then 0 else sol[|sol| - 1] * p.weights[|sol| - 1] + computeWeight(p.weights, sol, |sol| - 1 - 1);
  //   assert weight(p, sol) <= if |sol| == 0 then 0 else computeWeight(p.weights, sol, |sol| - 1);
  // } else {
  //   // assume computeWeight(p.weights, sol, |sol[..|sol| - 1]|) == if |sol[..|sol| - 1]| == 0 then 0 else sol[|sol[..|sol| - 1]|] * p.weights[|sol[..|sol| - 1]|] + computeWeight(p.weights, sol, |sol[..|sol| - 1]| - 1);
  //   // assume weight(p, sol[..|sol| - 1]) <= if |sol| == 0 then 0 else computeWeight(p.weights, sol, |sol| - 1);
  //   // isPartialSolutionLemma(p, sol[..|sol| - 1]);
  //   // assert weight(p, sol[..|sol| - 1]) <= p.knapsackCapacity;
  //   assert computeWeight(p.weights, sol, |sol| - 1) == if |sol| == 0 then 0 else sol[|sol| - 1] * p.weights[|sol| - 1] + computeWeight(p.weights, sol, |sol| - 1);
  //   assert weight(p, sol) <= if |sol| == 0 then 0 else computeWeight(p.weights, sol, |sol| - 1);
  //   isPartialSolutionLemma(p, sol[1..]);
  //   assert [sol[0]] + sol[1..] == sol;
  //   assert weight(p, [sol[0]]) + weight(p, sol[1..]) == weight(p, sol);
  //   assert weight(p, sol[1..]) <= p.knapsackCapacity;
  // }
}

// lemma gainOfSol(p: Problem, sol: seq<int>, partialProfit: int)
//   requires isValidProblem(p)
//   requires isValidPartialSolution(p, sol)
//   requires forall i :: 0 <= i < |sol| ==> sol[i] == 0
//   ensures gain(p, sol) == partialProfit
// {

// }

method getPartialSolution(p: Problem, profits: seq<seq<int>>) returns (solution: seq<int>)
    requires isValidProblem(p)
    requires 2 <= |profits| <= |p.weights| + 1
    requires 2 <= |profits| <= p.numberOfObjects + 1
    requires forall k :: 0 <= k < |profits| ==> 1 <= |profits[k]| <= p.knapsackCapacity + 1
    ensures hasOnlyPermittedValues(solution)
    ensures |solution| == p.numberOfObjects
{
    solution := [];

    var i := |profits| - 1;
    var j := |profits[i]| - 1;

    var lengthSol := |solution|;
    var lengthI := i;

    while i > 0 && j > 0
      invariant 0 <= i <= |profits| - 1
      invariant 0 <= i <= |p.weights|
      invariant 0 <= j <= |profits[i]| - 1
      invariant hasOnlyPermittedValues(solution)
      invariant 0 <= i <= p.numberOfObjects
      invariant |solution| > 0 ==> lengthSol + 1 == |solution|
      invariant |solution| > 0 ==> lengthI - 1 == i
      invariant i + |solution| <= p.numberOfObjects 
      invariant |profits| <= p.numberOfObjects + 1 ==> i <= p.numberOfObjects 
      invariant i == 0 ==> |solution| <= p.numberOfObjects
      invariant 0 <= |solution| <= p.numberOfObjects
      decreases i
      decreases j
    {
      lengthSol := |solution|;
      lengthI := i;
      assume 0 <= j < |profits[i - 1]|; //to be deleted
      if profits[i][j] == profits[i - 1][j] {
        solution := [0] + solution;
        i := i - 1;
      } else { 
        solution := [1] + solution;
        i := i - 1;
        if j - p.weights[i] >= 0 {
          j := j - p.weights[i];
        }
      } 
      assert i >= 0 && i <= |profits| - 1;
      assert i <= p.numberOfObjects; 
      assert lengthSol + 1 == |solution|; 
      assert |solution| >= 0;
      assert lengthI - 1 == i;

      assert 0 <= |solution| <= p.numberOfObjects;
    }  

    while j == 0 && i > 0 
      invariant hasOnlyPermittedValues(solution)
      invariant i + |solution| <= p.numberOfObjects 
      decreases i
    {
      solution := [0] + solution;
      i := i - 1;
    }
    assert 0 <= |solution| <= p.numberOfObjects;

    i := p.numberOfObjects - |solution|;
    while i > 0 && |solution| < p.numberOfObjects
      invariant hasOnlyPermittedValues(solution)
      invariant |solution| == p.numberOfObjects - i
      invariant 0 <= i
      invariant i == 0 ==> |solution| == p.numberOfObjects
      decreases i
    {
      solution := solution + [0];
      i := i - 1;
    }
    assert i == 0;
    assert |solution| == p.numberOfObjects;
}

method Main()
{
    var problem: Problem := Problem(numberOfObjects := 4, knapsackCapacity := 8, 
                                    gains := [1, 2, 5, 6], weights := [2, 3, 4, 5]);
    // var solution := getMaximProfit(problem);

    print "Maxim profit: ";
    // print gain(problem, solution);
    print "\n";
}