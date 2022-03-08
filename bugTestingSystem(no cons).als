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
	priorityLevel: one Priority,
}

sig TestCase {
	priorityLevel: one Priority, 
	desc: disj one Description, 
	expectedOutput: one Output,
	faults: set Failure
}

sig Output, Description, Resolution {}

//sig TestPackage {
//	allTestCases: Feature, //we had some Feature and Some story (this is not specified properly)
//	dependencies: TestPackage -> TestPackage
//} //all test cases developed are refered to as a testPackage

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

//no two testCases should have the same description
fact uniqueDescriptionForEachTestCase{
	no disj testCaseA, testCaseB : TestCase | some testCaseA.desc & testCaseB.desc
}

//there should be no test case that is not related to a story 
//for every test case there must be some story that has it associated with it
fact noLooseTestCase{
	all tc: TestCase|some s:Story| tc in s.testCases //I THINK THIS WORKS - KAYVIA
}

//a story can only belong to one feature
fact storyOnlyOneFeature{
	all story: Story | one feat: Feature | story in feat.stories
} 

//each story should belong to a feature 
fact noLooseStory{
	all story: Story | some feat: Feature| story in feat.stories
}

//no two stories should share any test cases
fact noSameTestCaseforStory{
	all disj s1,s2: Story | no s1.testCases & s2.testCases
}

//A failure should be related to the test case that discovered it


/* Can we get an instance of all the relations in the model? */
pred sanityCheck {
	one System
	some Feature
	some Story
	some TestCase
	some Output 
	some Failure
	some Description
	some Resolution} 
run sanityCheck for 2 but 5 TestCase
