import POGReader_.Parser
import POGReader_.Extractor

namespace B.POG
  @[always_inline]
  def parseAndExtractGoals (path : System.FilePath) : IO (Array Goal) :=
    extractGoals <$> parse path
end B.POG
