module bugTrackingSystem

sig Feature{stories: set Story}

abstract sig Priority {}
one sig Low, Medium, High extends Priority {}

abstract sig Severity {}
one sig Minor, Major, Critical extends Severity {}

abstract sig State {}
one sig Unresolved, WorkInProgress, Resolved extends State {}


sig Story {
	testCases: disj set TestCase, 
	//priorityLevel: one Priority
	
}

sig TestCase {
	//priorityLevel: one Priority, 
	//desc: disj one Description, 
	//expectedOutput: one Output
}


pred show {
	some Feature
	some Story
}

run show for 2 but 5 Feature
