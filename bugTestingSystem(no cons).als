module bugTrackingSystem

// SYSTEM ELEMENTS
//one sig System { TPs: seq TestPackage, reliabilityStat: one ReliabilityStatus }
one sig System { allFeatures: some Feature, reliabilityStat: one ReliabilityStatus }

sig Feature {stories: set Story}

abstract sig Priority {}
one sig Low, Medium, High extends Priority {}

abstract sig Severity {}
one sig Minor, Major, Critical extends Severity {}

abstract sig State {}
one sig Unresolved, WorkInProgress, Resolved extends State {}

//could have a description 
//Calculator and I want to add negative numbers
sig Story {
	testCases: disj set TestCase, 
	priorityLevel: one Priority
}

sig TestCase {
	priorityLevel: one Priority, 
	desc: disj one Description, 
	expectedOutput: one Output
}

sig Output, Description, Resolution {}

sig TestPackage {
	allTestCases: Feature->Story, //we had some Feature and Some story (this is not specified properly)
	dependencies: TestPackage -> TestPackage
} //all test cases developed are refered to as a testPackage

//let resolution be a set amount of time
//we had resolutionPeriod, figure out how this works first. Ask Ms
sig Failure {
	severityLevel: one Severity, 
	resolution: Failure -> lone Resolution, 
	description: one Description, 
	state: one State
} 

sig ReliabilityStatus {}


/* Can we get an instance of all the relations in the model? */
pred sanityCheck {
	one System
	some Feature
	some Story
	some TestCase
	some Output 
	some Failure
	some Description
	some Resolution
	some TestPackage} 
run sanityCheck for 2 expect 0
run sanityCheck for 3 expect 1 
