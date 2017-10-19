SetCompressor lzma

; VERSION and BITS should be passed as an argument at compile time using:
;      makensis -DVERSION=1.6 -DBITS=32 win-installer.nsi

!define MY_PRODUCT "Coq" ;Define your own software name here
!define SRC "C:\coq${BITS}\lib\user-contrib\mathcomp\"
!define OUTFILE "ssreflect-mathcomp-installer-${VERSION}-win${BITS}.exe"

!include "MUI2.nsh"

;--------------------------------
;Configuration

  Name "Ssreflect and the Mathematical Components library"

  ;General
  OutFile "${OUTFILE}"

  ;Folder selection page
  InstallDir "C:\Coq"
  
  ;Remember install folder
  InstallDirRegKey HKCU "Software\Coq" ""

;--------------------------------
;Modern UI Configuration

  !insertmacro MUI_PAGE_WELCOME
  !insertmacro MUI_PAGE_LICENSE ".\CeCILL-B"
  !insertmacro MUI_PAGE_COMPONENTS
  !define MUI_DIRECTORYPAGE_TEXT_TOP "Select where Coq is installed."
  !insertmacro MUI_PAGE_DIRECTORY
  !insertmacro MUI_PAGE_INSTFILES
  !insertmacro MUI_PAGE_FINISH
  
  !insertmacro MUI_UNPAGE_WELCOME
  !insertmacro MUI_UNPAGE_CONFIRM
  !insertmacro MUI_UNPAGE_INSTFILES
  !insertmacro MUI_UNPAGE_FINISH  

;--------------------------------
;Languages
 
  !insertmacro MUI_LANGUAGE "English"
  
;--------------------------------
;Language Strings

  ;Description
  LangString DESC ${LANG_ENGLISH} "The Ssreflect proof language and the Mathematical Components library."

;--------------------------------
;Installer Sections


Section "Ssreflect and MathComp" Sec

  SetOutPath "$INSTDIR\lib\user-contrib\mathcomp\"

  File /r ${SRC}\*.vo
  File /r ${SRC}\*.v
  File /r ${SRC}\*.glob

  CreateDirectory "$SMPROGRAMS\Coq"

  WriteINIStr "$SMPROGRAMS\Coq\The Mathematical Components Library.url" "InternetShortcut" "URL" "http://math-comp.github.io/math-comp/"

  WriteINIStr "$SMPROGRAMS\Coq\The Ssreflect User Manaul.url" "InternetShortcut" "URL" "http://hal.inria.fr/inria-00258384/en"
        
  SetOutPath "$INSTDIR"
  writeUninstaller "Uninstall Ssreflect and MathComp.exe"

SectionEnd

!insertmacro MUI_FUNCTION_DESCRIPTION_BEGIN
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec} $(DESC)
!insertmacro MUI_FUNCTION_DESCRIPTION_END
 
Section "Uninstall"

  RMDir /r "$INSTDIR\lib\user-contrib\mathcomp\"

  Delete "$SMPROGRAMS\Coq\The Mathematical Components Library.url"
  Delete "$SMPROGRAMS\Coq\The Ssreflect User Manaul.url"

  Delete "$INSTDIR\Uninstall Ssreflect and MathComp.exe"
  
SectionEnd
