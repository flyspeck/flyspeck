<?php
class TwelfUpload extends SpecialPage
{
        function TwelfUpload() {
                SpecialPage::SpecialPage("TwelfUpload", "import");
                self::loadMessages();
        }

	function createPage($title, $comment, $wikiText) {
		global $wgUser;

		$revision = new WikiRevision;
		$revision->setUsername($wgUser->getName());
		$revision->setTitle($title);
		$revision->setTimestamp(wfTimestampNow());
		$revision->setComment($comment);
		$revision->setMinor(false);
		$revision->setText($wikiText);

		$dbw = wfGetDB(DB_MASTER);
		$result = $dbw->deadlockLoop(array(&$revision, 'importOldRevision'));
		if ($result) {
			$nullRevision = Revision::newNullRevision($dbw, $title->getArticleId(), $comment, false);
			$nullRevision->insertOn($dbw);
			$article = new Article($title);
			$article->updateRevisionOn($dbw, $nullRevision);
		}
		return $result;
	}

 	function importPage($page, $filename, $wikiText = '') {
		global $wgUser, $wgOut;

		global $wgShowExceptionDetails;
		$wgShowExceptionDetails = true;

		/* get the metadata */
		switch ($page->tagName) {
			case 'section':
				if (preg_match('/^([^: ]+) ?:/', $wikiText, $matches)) {
					/* modeled to fit $wgLegalTitle */
					$title = str_replace(array('_', '[', ']', '{', '}', '|', '#', '<', '>', '%', '+', '?'),
					         	     array('_usc', '_sbo', '_sbc', '_cbo', '_cbc', '_bar', '_hash', '_lt', '_gt', '_pct', '_plus', '_q'), $matches[1]);
					/* pad the actual Twelf listing with spaces for listing formatting and escape other wiki formatting */
					$wikiText = preg_replace('/^(.*)$/me', '" " . wfEscapeWikiText("$1")', $wikiText);
					// TODO tokenize the text, replacing symbols by links to their respective pages. Note that then only the text _between_ these tokens has to be escaped!
					/* prepend the actual title, if the title was rewritten */
					if ($title != $matches[1]) {
						$wikiText = "'''''Actual title of this page: " . wfEscapeWikiText($matches[1]) . "'''''\n----\n" . $wikiText;
					}
				}
				else {
					return false;
					// FIXME throw some exception
				}
				$topic = $page->getAttribute('topic');
				$wikiText .= "\n[[Category:$topic]]";
				$twelfTitle = Title::newFromText(TWELF_PROJECT . '/' . $title . '.elf');
				// TODO add an auto-generated category like Lemma/Type/...?
				// lemma-... : ~~> Lemma
				// xyz : a -> b ~~> Function
				// xyz : ~~> Type
				break;
			case 'topic':
				$title = 'Category:' . $page->getAttribute('name');
				$wikiText = '[[Category:' . $page->getAttribute('parent') . ']]';
				$twelfTitle = Title::newFromText(TWELF_PROJECT . '/' . $title);
				break;
			default:
				// does not occur with the current implementation of execute
		}

		/* add/overwrite the Twelf page itself */
		$comment = wfMsgForContent('twelfupload-upload-twelf-comment', $filename);

		if (self::createPage($twelfTitle, $comment, $wikiText)) {
			$log = new LogPage('twelfupload');
			$log->addEntry('upload-twelf', $twelfTitle, "");
			// TODO use different message if category is created

			if ($page->tagName == 'section') {
				/* fake reference to a TeX page */
				$texTitle = Title::newFromText(TWELF_PROJECT . '/' . $title . '.tex');

				/* add the container page for annotations, if it does not yet exist */
				$title = Title::newFromText(TWELF_PROJECT . "/$title");
				if (!$title->exists()) {
					$comment = wfMsgForContent('twelfupload-create-container-comment', $filename);
					$wikiText = <<<EOT
== [[written in::Twelf]] ==
{{:$twelfTitle}}

== LaTeX ==
{{:$texTitle}}

== Annotations ==

EOT;

					if (self::createPage($title, $comment, $wikiText)) {
						$log->addEntry('create-container', $title, "");
					}
				}

				$wgOut->addHTML('<li><a href="' . $title->getLocalUrl() . '">' . $title . '</a></li>');
			}
		}
	}
 
        function execute( $par ) {
                global $wgRequest, $wgOut;
 
                $this->setHeaders();
 
		if ($wgRequest->wasPosted() && $wgRequest->getVal('action') == 'submit') {
			$source = ImportStreamSource::newFromUpload("twelffile");
			$filename = $_FILES['twelffile']['name'];
			
			if (WikiError::isError($source)) {
				$wgOut->addWikiText(wfEscapeWikiText($source->getMessage()));
			}
			else {
				/* Accessing mHandle is dirty, but allows us to
				 * reuse ImportStreamSource */
				$handle = $source->mHandle;
				$wgOut->addHTML("<p>Imported:</p><ul>");
				while (!feof($handle)) {
					// We assume that the lines of the file are quite short
					$buffer = fgets($handle);
					if (preg_match('/^%% ((?:section|topic).*)$/', $buffer, $matches)) {
						if ($page) {
							self::importPage($page, $filename, $wikiBuffer);
						}
						/* treat the section separator as an XML element to accommodate parsing */
						$dom = new DOMDocument();
						$dom->loadXML("<$matches[1]/>");
						$page = $dom->documentElement;
						$wikiBuffer = "";
					}
					else {
						$wikiBuffer .= $buffer;
					}
			    	}
				if ($page) {
					self::importPage($page, $filename, $wikiBuffer);
				}
			        fclose($handle);
				$wgOut->addHTML("</ul>");
			}
		}
		else {
			$action = $this->getTitle()->getLocalUrl('action=submit');
			$wgOut->addHTML(<<<EOH
<form action="{$action}" method="post" enctype="multipart/form-data">
<input type="hidden" name="MAX_FILE_SIZE" value="1048576" />
<label for="#twelffile">Twelf file:</label>
<input type="file" name="twelffile" id="twelffile"/><br/>
<input type="submit"/>
</form>
EOH
			);
		}
        }
 
        function loadMessages() {
                static $messagesLoaded = false;
                global $wgMessageCache;
                if ( !$messagesLoaded ) {
                        $messagesLoaded = true;
 
                        require( dirname( __FILE__ ) . '/TwelfUpload.i18n.php' );
                        foreach ( $allMessages as $lang => $langMessages ) {
                                $wgMessageCache->addMessages( $langMessages, $lang );
                        }
                }
                return true;
        }
}
