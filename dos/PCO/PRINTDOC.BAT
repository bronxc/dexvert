echo off
cls
echo �
echo This Batch file will print the Outline! documentation file MANUAL.DOC
echo to printer port LPT1:.
echo �
echo Press any key to begin (^Break to Abort)
echo �
pause
echo �
echo      Now printing . . . .
copy manual.doc lpt1:
echo �
echo      Printing complete
echo �

