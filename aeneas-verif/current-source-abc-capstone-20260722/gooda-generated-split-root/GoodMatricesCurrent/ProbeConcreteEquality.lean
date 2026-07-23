import AspisFormal.V5ComponentADeployedTerminalApplicability

open AspisV5ComponentADeployedTerminalApplicability

example :
    selectedTerminalMinor
        ConcreteProbeWitness.concreteSchedule (0, 0) (0, 0) =
      ConcreteProbeWitness.printedTerminalMatrix (0, 0) (0, 0) := by
  decide
