import pandas as pd
import os

def ensure_dir(f):
    d = os.path.dirname(f)
    if not os.path.exists(d):
        os.makedirs(d)

dfburst=pd.read_csv("code/generated-data/postconditional.csv")
dfleon=pd.read_csv("synquid/generated-data/data.csv")
dfsynquid=pd.read_csv("leon/generated-data/data.csv")
result1=dfburst.merge(dfleon,on="Test",how="outer")
result2=result1.merge(dfsynquid,on="Test",how="outer")
ensure_dir("generated-data/")
result2.to_csv("generated-data/postconditional.csv")

dfex=pd.read_csv("code/generated_data/examples.csv")
dfcorrect=pd.read_csv("code/manual-data/examples.csv")
result=dfex.merge(dfcorrect,on="Test",how="outer")
result.to_csv("generated-data/examples.csv")
