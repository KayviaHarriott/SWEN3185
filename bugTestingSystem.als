module bugTrackingSystem

//imports

//open util/graph[Parish] as pg
//open util/graph[Town] as tg

one sig System {TPs: seq TestPackage}
sig Feature {a: set Story}

sig Story {testCases: set TestCase, a: one Priority} //could have a description 
//Calculator and I want to add negative numbers

sig TestCase {a: one Priority, b: Description, expectedOutput: Output}

sig Output {}

sig Description {}

sig Resolution {} //for a failure, not a story

sig TestPackage {allTestCases: Feature -> Story, //we had some Feature and Some story
	dependencies: TestPackage -> TestPackage
} //all test cases developed are refered to as a testPackage


sig Failure {a: one Severity, b: Failure -> lone Resolution, c: one Description, states: one State} 
//let resolution be a set amount of time
//we had resolutionPeriod, figure out how this works first. Ask Ms

sig ReliabilityStatus {}

abstract sig Priority {}
one sig Low, Medium, High extends Priority {}

abstract sig Severity {}
one sig Minor, Major, Critical extends Severity {}

abstract sig State {}
one sig Unresolved, WorkInProgress, Resolved extends State {}
//mappings


//Feature: add two numbers
//Story: add 1 + 1
//Test Case: add 2 + 2, add 3 + 3
//Test Package: {add 2 + 2, add 3 + 3}
