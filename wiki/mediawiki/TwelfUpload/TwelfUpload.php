<?php
# Alert the user that this is not a valid entry point to MediaWiki if they try
# to access the skin file directly.
if (!defined('MEDIAWIKI')) {
        echo <<<EOT
To install the Twelf Upload extension, put the following line in LocalSettings.php:
require_once( "$IP/extensions/TwelfUpload/TwelfUpload.php" );
EOT;
        exit( 1 );
}
 
define("TWELF_PROJECT", "Flyspeck");

$wgAutoloadClasses['TwelfUpload'] = dirname(__FILE__) . '/TwelfUpload_body.php'; # Tell MediaWiki to load the extension body.
$wgSpecialPages['TwelfUpload'] = 'TwelfUpload'; # Let MediaWiki know about your new special page.
$wgExtensionFunctions[] = 'efTwelfUploadSetup';
$wgHooks['LoadAllMessages'][] = 'TwelfUpload::loadMessages'; # Load the internationalization messages for your special page.
$wgHooks['LanguageGetSpecialPageAliases'][] = 'efTwelfUploadLocalizedPageName'; # Add any aliases for the special page.
$wgExtensionCredits['TwelfUpload'][] = array(
        'name' => 'Twelf Upload',
        'version' => 0.1,
        'author' => 'Christoph Lange',
        'url' => 'http://kwarc.info/clange/',
        'description' => 'Upload a list of Twelf expressions.',
);
 
function efTwelfUploadSetup() {
	# The localized title of the special page is among the messages of the extension:
	TwelfUpload::loadMessages();

	# Add a new log type
	global $wgLogTypes, $wgLogNames, $wgLogHeaders, $wgLogActions;
	$wgLogTypes[] = 'twelfupload';
	$wgLogNames['twelfupload'] = 'twelfupload-logpagename';
	$wgLogHeaders['twelfupload'] = 'twelfupload-logpagetext';
	$wgLogActions['twelfupload/upload-twelf'] = 'twelfupload-logentry-upload-twelf-detail';
	$wgLogActions['twelfupload/create-container'] = 'twelfupload-logentry-create-container-detail';
}

function efTwelfUploadLocalizedPageName(&$specialPageArray, $code) {
  $text = wfMsg('twelfupload');
 
  # Convert from title in text form to DBKey and put it into the alias array:
  $title = Title::newFromText($text);
  $specialPageArray['TwelfUpload'][] = $title->getDBKey();
 
  return true;
}
