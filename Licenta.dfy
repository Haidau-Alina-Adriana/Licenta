datatype Problem = Problem(numberOfObjects: int, knapsackCapacity: int, gains: seq<int>, weights: seq<int>)

predicate hasPositiveValues(input: seq<int>)
{
    forall i :: 0 <= i < |input| ==> input[i] > 0
}

function max(p1: int, p2: int): int
{
    if p1 > p2 then p1 else p2
}

function gain(problem: Problem, solution: seq<int>): int
  requires isValidProblem(problem)
  requires isValidPartialSolution(problem, solution)
{
  if |solution| == 0 then 0 else computeGain(problem.gains, solution, |solution| - 1)
}

function computeGain(gains: seq<int>, solution: seq<int>, i: int) : int
  requires 0 <= i < |solution|
  requires 0 <= i < |gains|
{
   if i == 0 then 0 else solution[i] * gains[i] + computeGain(gains, solution, i - 1)
}

function intermediaryPartialSolution(seq1: seq<int>, seq2: seq<int>) : int
{
  if |seq1| == 0 || |seq2| == 0 then 0 else seq1[0] * seq2[0] + intermediaryPartialSolution(seq1[1..], seq2[1..])
}

function weight(problem: Problem, solution: seq<int>): int
  requires isValidProblem(problem)
  requires isValidPartialSolution(problem, solution)
{
  if |solution| == 0 then 0 else computeWeight(problem.weights, solution, |solution| - 1)
}

function computeWeight(weights: seq<int>, solution: seq<int>, i: int) : int
  requires 0 <= i < |solution|
  requires 0 <= i < |weights|
{
   if i == 0 then 0 else solution[i] * weights[i] + computeWeight(weights, solution, i - 1)
}

predicate isValidProblem(problem: Problem)
{
    |problem.gains| == |problem.weights| == problem.numberOfObjects && 
    problem.numberOfObjects > 0 && problem.knapsackCapacity >= 0 && 
    hasPositiveValues(problem.gains) && hasPositiveValues(problem.weights) 
}

predicate isValidSolution(problem: Problem, solution: seq<int>)
{
  isValidPartialSolution(problem, solution) &&
  |solution| == problem.numberOfObjects
}

predicate isSolution(p: Problem, solution: seq<int>)
  requires isValidProblem(p)
{
  isValidSolution(p, solution) &&
  weight(p, solution) <= p.knapsackCapacity
}

predicate isValidPartialSolution(problem: Problem, solution: seq<int>)
{
  0 <= |solution| <= problem.numberOfObjects && 
  forall k :: 0 <= k < |solution| ==> solution[k] == 0 || solution[k] == 1
}

predicate isPartialSolution(problem: Problem, solution: seq<int>)
  requires isValidProblem(problem)
{
  isValidPartialSolution(problem, solution) && 
  weight(problem, solution) < problem.knapsackCapacity
}

predicate isPartialSolutionOfProfitN(p: Problem, profits: seq<seq<int>>, x: int, y: int, n: int)
{
  0 <= x <= |profits| && (x > 0 ==> 0 <= y < |profits[x - 1]| && profits[x - 1][y] == n)
  //  0 <= x <= |profits| && (x > 0 ==> 0 <= y < |profits[x - 1]| && exists a: int :: profits[x - 1][y] == a)
}

// predicate isCompleteSolutionOfProfitX()
// {
  
// }

ghost predicate isOptimalSolution(problem: Problem, solution: seq<int>)
  requires isValidProblem(problem)
  requires isValidSolution(problem, solution)  
{
    isSolution(problem, solution) &&
    forall s: seq<int> :: (((isValidSolution(problem, s) && isSolution(problem, s)) ==> 
    gain(problem, solution) >= gain(problem, s)))
}

method addSequence(existingSeq: seq<seq<int>>, newSeq: seq<int>, c: int) returns (result: seq<seq<int>>)
  requires |newSeq| == c
  ensures result == existingSeq + [newSeq]
  ensures |result| == |existingSeq| + 1
{
  result := existingSeq + [newSeq];
}

method getMaximProfit(p: Problem) returns (solution: seq<int>)
  requires isValidProblem(p)
  // ensures isValidSolution(p, solution)
  // ensures isSolution(p, solution)
{
    var profits := []; 
    var maximProfit := 0;
    
    var partSol := getKnapsackObjects(p, profits);
    var N := intermediaryPartialSolution(partSol, p.gains); 

    var i := 0;
    while i <= p.numberOfObjects 
      invariant |profits| == i
      invariant 0 <= i <= p.numberOfObjects + 1
      invariant |profits| <= p.numberOfObjects + 1
      invariant forall k :: 0 <= k < i ==> |profits[k]| == p.knapsackCapacity + 1
      invariant forall x :: 0 <= x < i ==> forall y :: 0 <= y <= p.knapsackCapacity ==> 
        isPartialSolutionOfProfitN(p, profits, x, y, N)
    {
        var partialProfits := getPartialProfits(p, profits, i);
        profits := addSequence(profits, partialProfits, p.knapsackCapacity + 1);
        i := i + 1;

        partSol := getKnapsackObjects(p, profits);
        N := intermediaryPartialSolution(partSol, p.gains); 
    }

    maximProfit := profits[p.numberOfObjects][p.knapsackCapacity];

    solution := getKnapsackObjects(p, profits);
}

method getPartialProfits(p: Problem, profits: seq<seq<int>>, i: int) returns (partialProfits: seq<int>)
  requires isValidProblem(p)
  requires |profits| == i
  requires 0 <= i < p.numberOfObjects + 1
  requires forall k :: 0 <= k < i ==> |profits[k]| == p.knapsackCapacity + 1
  ensures |partialProfits| == p.knapsackCapacity + 1
  // ensures isSolution(p, solution)
{
        partialProfits := [];
        var j := 0;

        var partSol := getKnapsackObjects(p, profits);
        var N := intermediaryPartialSolution(partSol, p.gains); 

        while j <= p.knapsackCapacity
          invariant 0 <= j <= p.knapsackCapacity + 1
          invariant |partialProfits| == j
          invariant forall y :: 0 <= y < j ==> isPartialSolutionOfProfitN(p, profits, i, y, N)
        {
          if i == 0 || j == 0 {
              partialProfits := partialProfits + [0];
          } else {
            if p.weights[i - 1] <= j {
              partialProfits := partialProfits + [max(p.gains[i - 1] + profits[i - 1][j - p.weights[i - 1]], profits[i - 1][j])];
            } else {
              partialProfits := partialProfits + [profits[i - 1][j]];
            }
          }
          j := j + 1;
          partSol := getKnapsackObjects(p, profits);
          N := intermediaryPartialSolution(partSol, p.gains); 
        }
}

// method getKnapsackObjects(p: Problem, profits: seq<seq<int>>) returns (solution: seq<int>)
//   requires isValidProblem(p)
//   requires |profits| == p.numberOfObjects + 1
//   requires forall k :: 0 <= k <= p.numberOfObjects ==> |profits[k]| == p.knapsackCapacity + 1
//   ensures isValidSolution(p, solution)
// {
//     solution := [];
//     var i := p.numberOfObjects;
//     var j := p.knapsackCapacity;

//     while i > 0 && j >= 0
//       invariant 0 <= i <= p.numberOfObjects
//       invariant 0 <= j <= p.knapsackCapacity
//       invariant |solution| == p.numberOfObjects - i
//       invariant isPartialSolution(p, solution)
//       decreases i
//       decreases j
//     {
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
//     }
// }

method getKnapsackObjects(p: Problem, profits: seq<seq<int>>) returns (solution: seq<int>)
    requires isValidProblem(p)
    requires forall k :: 0 <= k < |profits| ==> |profits[k]| == p.knapsackCapacity + 1
    requires |profits| <= |p.weights| + 1
{
    solution := [];
    var i := |profits| - 1;
    var j := p.knapsackCapacity;

    while i > 0 && j >= 0
      invariant -1 <= i <= |profits|
      invariant 0 <= j <= p.knapsackCapacity
      invariant -1 <= i <= |p.weights|
      invariant |solution| <= p.numberOfObjects - i
      invariant isPartialSolution(p, solution)
      decreases i
      decreases j
    {
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
    }
}

method Main()
{
    var problem: Problem := Problem(numberOfObjects := 4, knapsackCapacity := 8, 
                                    gains := [1, 2, 5, 6], weights := [2, 3, 4, 5]);
    var solution := getMaximProfit(problem);

    print "Maxim profit: ";
    // print gain(problem, solution);
    print "\n";
}