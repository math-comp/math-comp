SetCompressor lzma

; The VERSION should be passed as an argument at compile time using :
;      nsis -DVERSION=1.5 win-installer.nsi

!define MY_PRODUCT "Coq" ;Define your own software name here
!define SRC ".\"
!define SRC_SSR "C:\Coq\lib\user-contrib\Ssreflect\"
!define SRC_MC "C:\Coq\lib\user-contrib\MathComp\"
!define OUTFILE "ssr-mathcomp-installer-${VERSION}.exe"

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
  !insertmacro MUI_PAGE_LICENSE "${SRC}\CeCILL-B"
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
  LangString DESC_1 ${LANG_ENGLISH} "This package contains the Ssreflect proof language."
  LangString DESC_2 ${LANG_ENGLISH} "This package contains the Mathematical Components lirbary."

;--------------------------------
;Installer Sections


Section "Ssreflect" Sec1

  SetOutPath "$INSTDIR\lib\user-contrib\Ssreflect\"

  File /r ${SRC_SSR}\*.vo
  File /r ${SRC_SSR}\*.v
  File /r ${SRC_SSR}\*.glob
  File /r ${SRC_SSR}\*.cmx
  File /r ${SRC_SSR}\*.cmxs
  File /r ${SRC_SSR}\*.cmi

  CreateDirectory "$SMPROGRAMS\Coq"

  WriteINIStr "$SMPROGRAMS\Coq\The Ssreflect Library.url" "InternetShortcut" "URL" "http://ssr.msr-inria.inria.fr/doc/ssreflect-${VERSION}/"

  WriteINIStr "$SMPROGRAMS\Coq\The Ssreflect User Manaul.url" "InternetShortcut" "URL" "http://hal.inria.fr/inria-00258384/en"
        
  SetOutPath "$INSTDIR"
  writeUninstaller "Uninstall Ssreflect and MathComp.exe"

SectionEnd

Section "MathComp" Sec2

  SetOutPath "$INSTDIR\lib\user-contrib\MathComp\"

  File /r ${SRC_MC}\*.vo
  File /r ${SRC_MC}\*.v
  File /r ${SRC_MC}\*.glob
  File /r ${SRC_MC}\*.cmx
  File /r ${SRC_MC}\*.cmxs
  File /r ${SRC_MC}\*.cmi

  CreateDirectory "$SMPROGRAMS\Coq"

  WriteINIStr "$SMPROGRAMS\Coq\The Mathematical Components Library.url" "InternetShortcut" "URL" "http://ssr.msr-inria.inria.fr/doc/mathcomp-${VERSION}/"

SectionEnd

!insertmacro MUI_FUNCTION_DESCRIPTION_BEGIN
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec1} $(DESC_1)
  !insertmacro MUI_DESCRIPTION_TEXT ${Sec2} $(DESC_2)
!insertmacro MUI_FUNCTION_DESCRIPTION_END
 
Section "Uninstall"

  RMDir /r "$INSTDIR\lib\user-contrib\MathComp\"
  RMDir /r "$INSTDIR\lib\user-contrib\Ssreflect\"

  Delete "$SMPROGRAMS\Coq\The Mathematical Components Library.url"
  Delete "$SMPROGRAMS\Coq\The Ssreflect Library.url"
  Delete "$SMPROGRAMS\Coq\The Ssreflect User Manaul.url"

  Delete "$INSTDIR\Uninstall Ssreflect and MathComp.exe"
  
SectionEnd
