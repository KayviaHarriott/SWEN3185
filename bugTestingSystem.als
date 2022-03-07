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
	testCases: disj set TestCase, 
	priorityLevel: one Priority
}

sig TestCase {
	priorityLevel: one Priority, 
	desc: disj one Description, 
	expectedOutput: one Output
}

sig Output, Description, Resolution {}

//sig TestPackage {
//	allTestCases: Feature->Story, //we had some Feature and Some story (this is not specified properly)
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

//there should be no test case that is not related to a story 
//for every test case there must be some story that has it associated with it
fact noLooseTestCase{
	all tc: TestCase|some s:Story| tc in s.testCases //I THINK THIS WORKS - KAYVIA
}

//no two stories should have the same test case
	//added disj to the set of test cases that a story should have to enforce this
fact noSameTestCaseforStory{
	//no disj storya, storyb : Story | some storya.TestCase //& storyb.TestCase
}


//no two testCases should have the same description
	//added disj to the one description that a testcase should have
fact uniqueDescriptionForEachTestCase{
	no disj testCaseA, testCaseB : TestCase | some testCaseA.desc & testCaseB.desc
}


//a story can only belong to one feature
fact storyOnlyOneFeature{
	//all feature: Feature | lone feature.stories
} 

//a testcase can only belong to one test package (which implies that it cannot belong to another story outside of the test package)

//if it is that a testcase exists, a test package should exist 
fact testPackageExistIfTestCaseExist{
	
} 

//once a test package exist there must be some feature it realates to 

//there should be no empty test packages 
fact noEmptyTestPackages{
	
}

//each story should belong to a feature 
fact noLooseStory{
	//all story: Story | some feat: Feature| story in feat.stories
}

pred M2 () {}
//run f

run M2 for 3
//A failure should be related to the test case that discovered it 
