module bugTrackingSystem

// SYSTEM ELEMENTS
//one sig System { TPs: seq TestPackage, reliabilityStat: one ReliabilityStatus }
one sig System { allFeatures: Feature, reliabilityStat: one ReliabilityStatus }

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
	testCases: set TestCase, 
	priorityLevel: one Priority
}

sig TestCase {
	priorityLevel: one Priority, 
	b: lone Description, 
	expectedOutput: one Output
}

sig Output, Description, Resolution {}

sig TestPackage {
	allTestCases: Feature -> Story, //we had some Feature and Some story
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

//FACTS

//there should be no test case that is not related to a story 
fact noLooseTestCase{
	all tc: TestCase| some story: Story | some  story->tc
}

//two stories should not have the same test case

//two storties should not have the same description

//a story can only belong to one feature 

//a testcase can only belong to one test package (which implies that it cannot belong to another story outside of the test package)

//if it is that a testcase exists, a test package should exist 

//once a test package esist there must be some feature it realates to 

//there should be no empty tets packages 

//each story should belong to a feature 
//fact noLooseStory{
//	all story: Story | some feat: Feature| some story->feat
//}

//A failure should be related to the test case that discovered it 
