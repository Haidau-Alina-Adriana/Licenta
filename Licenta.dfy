datatype Problem = Problem(numberOfObjects: int, knapsackCapacity: int, costs: seq<int>, weights: seq<int>)

datatype Solution = Solution(profit: int, objects: seq<int>)

predicate hasPositiveValues(input: seq<int>)
{
    forall i :: 0 <= i < |input| ==> input[i] > 0
}

predicate isValidProblem(p: Problem)
{
    |p.costs| == |p.weights| == p.numberOfObjects && p.numberOfObjects > 0 && p.knapsackCapacity >= 0 && 
          hasPositiveValues(p.costs) && hasPositiveValues(p.weights)
}

function max(p1: int, p2: int): int
{
    if p1 > p2 then p1 else p2
}

function gain(solution: seq<int>, costs: seq<int>): int
  requires |solution| == |costs| 
{
  if |solution| == 0 then 0 else solution[0] * costs[0] + gain(solution[1..], costs[1..])
}

predicate isValidSolution(p: Problem, solution: Solution)
{
  |solution.objects| == p.numberOfObjects && 
  forall k :: 0 <= k < |solution.objects| ==> solution.objects[k] == 0 || solution.objects[k] == 1
}

predicate isSolution(p: Problem, solution: Solution)
  requires isValidProblem(p)
  requires isValidSolution(p, solution) 
{
  gain(solution.objects, p.costs) == solution.profit
}

predicate isPartialSolution(partialSolution: seq<int>)
{
  forall s :: 1 <= s < |partialSolution| ==> partialSolution[s] >= partialSolution[s - 1]
}

predicate isOptimalSolution(p: Problem, solution: Solution)
  requires isValidProblem(p)
  requires isValidSolution(p, solution)  
{
    isSolution(p, solution) &&
    forall s : Solution :: ((isSolution(p, s) && isValidSolution(p, s)) 
    ==> gain(solution.objects, p.costs) >= gain(s.objects, p.costs))
}

method addSequence(existingSeq: seq<seq<int>>, newSeq: seq<int>, c: int) returns (result: seq<seq<int>>)
  requires |newSeq| == c
  ensures result == existingSeq + [newSeq]
  ensures |result| == |existingSeq| + 1
{
  result := existingSeq + [newSeq];
}

method getMaximProfit(p: Problem) returns (solution: Solution)
  requires isValidProblem(p)
  // ensures isSolution(p, solution)
{
    var profits := []; 
    var maximProfit := 0;
    var partialProfits := [];
    
    var i := 0;
    while i <= p.numberOfObjects 
      invariant |profits| == i
      invariant 0 <= i <= p.numberOfObjects + 1
      invariant forall k :: 0 <= k < i ==> |profits[k]| == p.knapsackCapacity + 1
      // invariant forall j :: 0 <= j < i ==> isPartialSolution(partialProfits)
    {
        partialProfits := getPartialProfits(p, profits,i);
        profits := addSequence(profits, partialProfits, p.knapsackCapacity + 1);
        i := i + 1;
    }

    maximProfit := profits[p.numberOfObjects][p.knapsackCapacity];

    var objects := getKnapsackObjects(p, profits, maximProfit);

    solution := Solution(maximProfit, objects);
}

method getPartialProfits(p: Problem, profits: seq<seq<int>>, i: int) returns (partialProfits: seq<int>)
  requires isValidProblem(p)
  requires |profits| == i
  requires 0 <= i < p.numberOfObjects + 1
  requires forall k :: 0 <= k < i ==> |profits[k]| == p.knapsackCapacity + 1
  ensures |partialProfits| == p.knapsackCapacity + 1
  // ensures isSolution(p, solution, maximProfit)
{
        partialProfits := [];
        var j := 0;
        while j <= p.knapsackCapacity
          invariant 0 <= j <= p.knapsackCapacity + 1
          invariant |partialProfits| == j
          // invariant isPartialSolution(partialProfits)
        {
          if i == 0 || j == 0 {
              partialProfits := partialProfits + [0];
          } else {
            if p.weights[i - 1] <= j {
              partialProfits := partialProfits + [max(p.costs[i - 1] + profits[i - 1][j - p.weights[i - 1]], profits[i - 1][j])];
            } else {
              partialProfits := partialProfits + [profits[i - 1][j]];
            }
          }
          j := j + 1;
        }
}

method getKnapsackObjects(p: Problem, profits: seq<seq<int>>, maximProfit: int) returns (objectHasBeenAdded: seq<int>)
  requires isValidProblem(p)
  requires |profits| == p.numberOfObjects + 1
  requires forall k :: 0 <= k <= p.numberOfObjects ==> |profits[k]| == p.knapsackCapacity + 1
  // ensures isSolution(p, solution)
{
    objectHasBeenAdded := [];
    var i := p.numberOfObjects;
    var j := p.knapsackCapacity;

    while i > 0 && j >= 0
      invariant 0 <= i <= p.numberOfObjects
      invariant 0 <= j <= p.knapsackCapacity
      invariant |objectHasBeenAdded| == p.numberOfObjects - i
      decreases i
      decreases j
    {
      if profits[i][j] == profits[i - 1][j] {
        objectHasBeenAdded := [0] + objectHasBeenAdded;
        i := i - 1;
      } else { 
        objectHasBeenAdded := [1] + objectHasBeenAdded;
        i := i - 1;
        if j - p.weights[i] >= 0 {
          j := j - p.weights[i];
        }
        
      }
    }
    // assert |objectHasBeenAdded| == |p.weights|;
}

method Main()
{
    var problem: Problem := Problem(numberOfObjects := 4, knapsackCapacity := 8, 
                                    costs := [1, 2, 5, 6], weights := [2, 3, 4, 5]);
    var solution := getMaximProfit(problem);

    print "Maxim profit: ";
    print solution.profit;
    print "\n";
}